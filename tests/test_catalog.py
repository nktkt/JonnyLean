"""Catalog and scope regressions without provider calls."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from tools.catalog import affected, changed_paths, generated, select
from tools.jonnylean import capture_inputs, capture_verification_inputs, load_task
from tools.scopes import check_compiled_graph, imports, module_graph
from tests.fixtures import core_only

PROJECT = Path(__file__).resolve().parents[1]


class CatalogTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='jonnylean-catalog-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / 'project'
        shutil.copytree(PROJECT, self.root, ignore=shutil.ignore_patterns(
            '.git', '.lake', '.jonnylean', 'artifacts', '__pycache__', '.jonnylean.lock'))
        core_only(self.root)
        self.tasks = load_task(self.root, 'JL-001')[0]['tasks']

    def fingerprints(self):
        return {t['id']: capture_inputs(self.root, t) for t in self.tasks}

    def test_changes_invalidate_dependents_only_but_all_mechanical_evidence(self):
        before = self.fingerprints()
        mechanical = capture_verification_inputs(self.root)
        path = self.root / 'JonnyLean/NumberTheory/Parity.lean'
        path.write_text(path.read_text() + '\n-- Changed dependency.\n')
        after = self.fingerprints()
        self.assertEqual([i for i in before if before[i] != after[i]], ['JL-001', 'JL-002', 'JL-003'])
        self.assertNotEqual(mechanical, capture_verification_inputs(self.root))
        self.assertEqual([t['id'] for t in affected(self.root, self.tasks, [str(path.relative_to(self.root))])],
                         ['JL-001', 'JL-002', 'JL-003'])

    def test_contract_change_affects_its_task_and_policy_affects_every_task(self):
        before = self.fingerprints()
        contract = self.root / 'contracts/JL002.lean'
        contract.write_text(contract.read_text() + '\n-- Contract edit.\n')
        after = self.fingerprints()
        self.assertEqual([i for i in before if before[i] != after[i]], ['JL-002'])
        config = self.root / 'jonnylean.toml'
        config.write_text(config.read_text().replace('timeout_seconds = 120', 'timeout_seconds = 121'))
        final = self.fingerprints()
        self.assertTrue(all(final[i] != after[i] for i in after))

    def test_catalog_sync_is_deterministic_and_detects_duplicate_declarations(self):
        first = generated(self.root)
        self.assertEqual(first, generated(self.root))
        self.assertEqual((self.root / 'jonnylean.toml').read_text(), first[0])
        fragment = self.root / 'catalog/fragments/core.json'
        tasks = json.loads(fragment.read_text())
        tasks[1]['declaration'] = tasks[0]['declaration']
        fragment.write_text(json.dumps(tasks))
        with self.assertRaisesRegex(ValueError, 'duplicate catalog declaration'):
            generated(self.root)

    def test_selection_and_compiled_dependency_crosscheck(self):
        self.assertEqual(len(select(self.tasks, domain='finite-sets')), 2)
        self.assertEqual(len(select(self.tasks, tag='cardinality')), 2)
        self.assertEqual(select(self.tasks, query='triangular_formula')[0]['id'], 'JL-003')
        graph = module_graph(self.root)
        audit = {'imports': [{'module': k, 'imports': v} for k, v in graph.items()]}
        check_compiled_graph(self.root, audit)
        audit['imports'][0]['imports'] = []
        with self.assertRaisesRegex(ValueError, 'disagree'):
            check_compiled_graph(self.root, audit)

    def test_header_reader_handles_nested_comments_and_lean_modifiers(self):
        path = self.root / 'sample.lean'
        path.write_text('/- outer /- nested -/ -/\nmodule\nprelude\npublic meta import all JonnyLean.A\n'
                        '-- another\nimport JonnyLean.B\nnamespace Foo\n')
        self.assertEqual(imports(path), ['JonnyLean.A', 'JonnyLean.B'])
        path.write_text('import «NonAscii»\n')
        with self.assertRaises(ValueError):
            imports(path)

    def test_changed_ref_tracks_untracked_files_and_rejects_bad_refs(self):
        def git(*args):
            subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True)
        git('init', '-q'); git('add', '.')
        git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid', 'commit', '-qm', 'fixture')
        self.assertEqual(changed_paths(self.root, 'HEAD'), [])
        (self.root / 'JonnyLean/New.lean').write_text('-- new file\n')
        self.assertEqual(changed_paths(self.root, 'HEAD'), ['JonnyLean/New.lean'])
        with self.assertRaises(ValueError):
            changed_paths(self.root, '--help')

    def test_worker_domain_filter_does_not_claim_unselected_tasks(self):
        from worker.engine import Engine
        engine = Engine(self.root)
        with patch.object(engine, 'create', return_value=None) as create:
            self.assertEqual(engine.work(domain='finite-sets', limit=5), [])
            self.assertEqual([c.args[0] for c in create.call_args_list], ['JL-004'])
        with patch.object(engine, 'create') as create:
            self.assertEqual(engine.work(domain='missing'), [])
            create.assert_not_called()

    def test_worker_review_prompt_scopes_types_but_keeps_global_evidence(self):
        from worker.engine import Engine
        engine = Engine(self.root)
        task = self.tasks[0]
        report = {'mechanical': 'pass', 'contract_audit': {'declarations': [{'name': 'Contract.target'}]},
                  'inputs': {'JonnyLean/NumberTheory/Parity.lean': 'fixture'},
                  'audit': {'modules': ['JonnyLean.NumberTheory.Parity', 'JonnyLean.FiniteSet.Basic'],
                            'declarations': [{'name': 'relevant', 'module': task['module']},
                                             {'name': 'unrelated', 'module': 'JonnyLean.FiniteSet.Basic'}]}}
        prompt = engine.review_prompt(task, report)
        evidence = json.loads(prompt.split('MECHANICAL EVIDENCE:\n')[1])
        self.assertEqual(evidence['global_audit']['declarations'], 2)
        self.assertEqual([d['name'] for d in evidence['declarations']], ['relevant'])
        self.assertEqual(evidence['contract_audit'], report['contract_audit'])
        # Read the candidate's recorded scope, even if the live project differs.
        report['inputs']['JonnyLean/FiniteSet/Basic.lean'] = 'candidate-dependency'
        evidence = json.loads(engine.review_prompt(task, report).split('MECHANICAL EVIDENCE:\n')[1])
        self.assertEqual([d['name'] for d in evidence['declarations']], ['relevant', 'unrelated'])

    def test_cli_empty_selection_reports_no_verification(self):
        result = subprocess.run([sys.executable, 'tools/jonnylean.py', 'verify', '--domain', 'missing',
                                 '--project', str(self.root)], cwd=PROJECT, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('no verification was performed', result.stdout)
        self.assertFalse((self.root / 'artifacts').exists())


if __name__ == '__main__':
    unittest.main()

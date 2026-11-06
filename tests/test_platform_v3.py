"""Real-Lean parallel verification plus read-only planning and library lookup."""
from contextlib import redirect_stdout
from io import StringIO
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from tests.fixtures import core_only
from tools.jonnylean import command_step, run_batch, run_one
from tools.library import current_declarations, search
from tools.planning import expand_dependencies, make_plan, shard

PROJECT = Path(__file__).resolve().parents[1]


class PlanningTests(unittest.TestCase):
    def setUp(self):
        self.tasks = [
            {'id': 'JL-001', 'domain': 'logic', 'depends_on': []},
            {'id': 'JL-002', 'domain': 'logic', 'depends_on': ['JL-001']},
            {'id': 'JL-003', 'domain': 'logic', 'depends_on': ['JL-001']},
            {'id': 'JL-004', 'domain': 'algorithms', 'depends_on': ['JL-002', 'JL-003']},
            {'id': 'JL-005', 'domain': 'algorithms', 'depends_on': []}]

    def test_dependency_diamond_is_expanded_once_and_ordered(self):
        result = make_plan(self.tasks, [self.tasks[3]], True)
        self.assertEqual(result['tasks'], ['JL-001', 'JL-002', 'JL-003', 'JL-004'])
        self.assertEqual(result['layers'], [['JL-001'], ['JL-002', 'JL-003'], ['JL-004']])
        self.assertEqual(result['prerequisites_outside_selection'], [])
        self.assertEqual(make_plan(self.tasks, [self.tasks[3]])['prerequisites_outside_selection'],
                         ['JL-002', 'JL-003'])

    def test_shards_partition_selection_deterministically(self):
        slices = [shard(self.tasks, f'{i}/3') for i in range(1, 4)]
        self.assertEqual(sorted(t['id'] for part in slices for t in part), [t['id'] for t in self.tasks])
        self.assertEqual(shard(list(reversed(self.tasks)), '2/3'), slices[1])
        self.assertEqual(shard(self.tasks, '6/6'), [])
        for bad in ('0/3', '4/3', '1/257', '1', '-1/3', '1/0'):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                shard(self.tasks, bad)

    def test_unknown_and_cyclic_dependencies_fail(self):
        with self.assertRaises(ValueError):
            expand_dependencies(self.tasks, ['JL-999'])
        self.tasks[0]['depends_on'] = ['JL-004']
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            make_plan(self.tasks, [self.tasks[3]], True)


class ParallelIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='jonnylean-v3-platform-')
        cls.addClassCleanup(cls.temp.cleanup)
        cls.parent = Path(cls.temp.name).resolve()
        cls.seed = cls.parent / 'seed'
        shutil.copytree(PROJECT, cls.seed, ignore=shutil.ignore_patterns(
            '.git', '.lake', '.jonnylean', 'artifacts', '__pycache__', '.jonnylean.lock'))
        core_only(cls.seed)

    def setUp(self):
        self.root = self.parent / self._testMethodName
        shutil.copytree(self.seed, self.root)

    def cli(self, *args, code=0):
        result = subprocess.run([sys.executable, str(self.root / 'tools/jonnylean.py'), *args,
                                 '--project', str(self.root)], cwd=self.root,
                                capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        return result

    def reports(self):
        return [json.loads(p.read_text()) for p in sorted((self.root / 'artifacts').glob('JL-*/report.json'))]

    def test_parallel_contracts_share_one_fresh_library_check_and_search_real_types(self):
        self.cli('verify', 'all', '--jobs', '3')
        reports = self.reports()
        self.assertEqual(len(reports), 5)
        self.assertTrue(all(r['status'] == 'pass' for r in reports))
        self.assertEqual([r['library_reused'] for r in reports], [False, True, True, True, True])
        self.assertTrue(all(r['verification_inputs'] == reports[0]['verification_inputs'] for r in reports))
        rows = current_declarations(self.root)
        found = search(rows, 'even_add', kind='theorem')
        self.assertEqual(found[0]['name'], 'JonnyLean.even_add')
        self.assertIn('JonnyLean.Even', found[0]['type'])
        self.assertEqual(search(rows, module='JonnyLean.NumberTheory.Parity', kind='theorem'), found)
        exported = self.cli('library', 'show', 'JonnyLean.even_add', '--format', 'json')
        self.assertEqual(json.loads(exported.stdout), found)
        batch = json.loads((self.root / 'artifacts/batch.json').read_text())
        self.assertTrue(batch['inputs_stable'])
        self.assertEqual(batch['jobs'], 3)
        self.assertEqual(set(batch['results'].values()), {0})
        source = self.root / 'JonnyLean/NumberTheory/Parity.lean'
        source.write_text(source.read_text() + '\n-- Changed source.\n')
        with self.assertRaisesRegex(ValueError, 'No current'):
            current_declarations(self.root)

    def test_one_bad_contract_does_not_skip_parallel_neighbors(self):
        source = self.root / 'contracts/JL003.lean'
        source.write_text(source.read_text() + '\nexample : False := by sorry\n')
        self.cli('verify', 'all', '--jobs', '3', code=2)
        self.assertEqual([r['status'] for r in self.reports()], ['pass', 'pass', 'error', 'pass', 'pass'])

    def test_failed_seed_contract_does_not_publish_library_evidence(self):
        source = self.root / 'contracts/JL001.lean'
        source.write_text(source.read_text() + '\naxiom FixtureForbidden : False\n')
        self.cli('verify', 'all', '--jobs', '3', code=1)
        reports = self.reports()
        self.assertEqual([r['status'] for r in reports], ['fail', 'pass', 'pass', 'pass', 'pass'])
        self.assertEqual([r['library_reused'] for r in reports], [False, False, True, True, True])

    def test_library_failure_is_reused_without_rebuilding_for_every_task(self):
        source = self.root / 'JonnyLean/NumberTheory/Parity.lean'
        source.write_text(source.read_text().replace('refine ⟨ka + kb, ?_⟩', 'exact False.elim True.intro'))
        with patch('tools.jonnylean.command_step', wraps=command_step) as commands, redirect_stdout(StringIO()):
            code = run_batch(self.root, ['JL-001', 'JL-002', 'JL-004'], 'verify', jobs=2)
        self.assertEqual(code, 2)
        self.assertEqual(sum(call.args[1][-1] == 'build' for call in commands.call_args_list), 1)
        self.assertTrue(all(r['mechanical'] != 'pass' for r in self.reports()))

    def test_batch_rejects_inter_task_source_change(self):
        def mutate_after_first(root, task_id, *args):
            code = run_one(root, task_id, *args)
            if task_id == 'JL-001':
                source = root / 'JonnyLean/NumberTheory/Parity.lean'
                source.write_text(source.read_text() + '\n-- Concurrent edit fixture.\n')
            return code
        with patch('tools.jonnylean.run_one', side_effect=mutate_after_first), redirect_stdout(StringIO()):
            self.assertEqual(run_batch(self.root, ['JL-001', 'JL-002', 'JL-004'], 'verify', jobs=2), 2)
        batch = json.loads((self.root / 'artifacts/batch.json').read_text())
        self.assertFalse(batch['inputs_stable'])
        self.assertEqual(batch['results']['JL-002'], 2)
        self.assertEqual(batch['results']['JL-004'], 2)

    def test_plan_and_shard_do_not_create_ai_state(self):
        result = self.cli('plan', 'JL-003', '--include-dependencies', '--format', 'json')
        self.assertEqual(json.loads(result.stdout)['tasks'], ['JL-001', 'JL-002', 'JL-003'])
        self.assertFalse((self.root / '.jonnylean').exists())
        self.assertFalse((self.root / 'artifacts').exists())
        self.cli('verify', 'all', '--shard', '2/2', '--jobs', '2')
        self.assertEqual([r['task'] for r in self.reports()], ['JL-002', 'JL-004'])

    def test_invalid_parallelism_and_shards_fail_before_checks(self):
        self.cli('verify', 'all', '--jobs', '0', code=2)
        self.cli('verify', 'all', '--shard', '3/2', code=2)
        self.assertFalse((self.root / 'artifacts').exists())


if __name__ == '__main__':
    unittest.main()

"""Distribution integration tests. Fixture reviews are synthetic, never approvals."""
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
import zipfile

from tests.fixtures import core_only
from tools.jonnylean import CRITERIA, run_batch, capture_inputs, load_task
from tools.release import build, check, collect, digest, encoded, readiness, source_names

PROJECT = Path(__file__).resolve().parents[1]


class ReleaseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='jonnylean-v4-release-')
        cls.addClassCleanup(cls.temp.cleanup)
        cls.parent = Path(cls.temp.name).resolve()
        cls.seed = cls.parent / 'seed'
        shutil.copytree(PROJECT, cls.seed, ignore=shutil.ignore_patterns(
            '.git', '.lake', '.jonnylean', 'artifacts', '__pycache__', '.jonnylean.lock'))
        core_only(cls.seed)
        config, _ = load_task(cls.seed, 'JL-001')
        for task in config['tasks']:
            (cls.seed / task['review']).write_bytes(encoded({
                'schema': 1, 'task': task['id'], 'decision': 'approve', 'findings': [],
                'reviewer': {'kind': 'ai', 'name': 'SYNTHETIC FIXTURE — not an independent review'},
                'inputs': capture_inputs(cls.seed, task),
                'checks': [{'criterion': criterion, 'result': 'pass',
                            'evidence': 'Synthetic release gate test, not a mathematical approval.'}
                           for criterion in sorted(CRITERIA)]}))
        with redirect_stdout(StringIO()):
            if run_batch(cls.seed, [t['id'] for t in config['tasks']], 'run', jobs=2):
                raise RuntimeError('Real Lean fixture verification failed')
        shutil.rmtree(cls.seed / '.lake')

    def setUp(self):
        self.root = self.parent / self._testMethodName
        shutil.copytree(self.seed, self.root)
        self.output = self.root / 'artifacts/release.zip'

    def rewrite_zip(self, path, transform):
        with zipfile.ZipFile(path) as archive:
            entries = {name: archive.read(name) for name in archive.namelist()}
        transform(entries)
        with zipfile.ZipFile(path, 'w') as archive:
            for name, data in entries.items():
                archive.writestr(name, data)

    def test_deterministic_archive_and_clean_source_reverification(self):
        first = build(self.root, self.output)
        second_path = self.root / 'artifacts/second.zip'
        second = build(self.root, second_path)
        self.assertEqual(first['sha256'], second['sha256'])
        self.assertEqual(self.output.read_bytes(), second_path.read_bytes())
        result = check(self.output, first['sha256'])
        self.assertEqual(result['integrity'], 'pass')
        self.assertFalse(result['fresh_verification_performed'])
        self.assertFalse(result['authenticated'])
        extracted = self.root / 'artifacts/extracted'
        with zipfile.ZipFile(self.output) as archive:
            names = archive.namelist()
            self.assertIn('source/contracts/JL001.lean', names)
            self.assertIn('evidence/library-audit.json', names)
            self.assertFalse(any('/.lake/' in n or '/.git/' in n or '/.jonnylean/' in n for n in names))
            # Only our own freshly generated and checked archive is extracted in this test.
            archive.extractall(extracted)
        source = extracted / 'source'
        run = subprocess.run([sys.executable, 'tools/jonnylean.py', 'run', 'all', '--jobs', '2'],
                             cwd=source, capture_output=True, text=True, timeout=120)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn('JL-005: PASS', run.stdout)

    def test_source_and_review_staleness_block_release(self):
        self.assertTrue(readiness(self.root)['ready'])
        path = self.root / 'JonnyLean/NumberTheory/Parity.lean'
        path.write_text(path.read_text() + '\n-- changed after verification\n')
        self.assertFalse(readiness(self.root)['ready'])
        with self.assertRaisesRegex(ValueError, 'requires current'):
            build(self.root, self.output)
        self.assertFalse(self.output.exists())
        self.assertFalse((self.root / '.jonnylean.lock').exists())

    def test_rejected_or_missing_review_blocks_even_with_passing_report(self):
        review = self.root / 'reviews/JL-003.json'
        record = json.loads(review.read_text())
        record['decision'] = 'request_changes'
        review.write_bytes(encoded(record))
        self.assertFalse(readiness(self.root)['ready'])
        review.unlink()
        with self.assertRaisesRegex(ValueError, 'JL-003'):
            collect(self.root)

    def test_missing_malformed_and_mismatched_report_blocks(self):
        path = self.root / 'artifacts/JL-002/report.json'
        for value in ('[]', '{}', '{'):
            path.write_text(value)
            self.assertFalse(readiness(self.root)['ready'])
        path.unlink()
        self.assertFalse(readiness(self.root)['ready'])

    def test_modified_entry_digest_is_rejected(self):
        build(self.root, self.output)
        self.rewrite_zip(self.output, lambda entries: entries.__setitem__('source/README.md', b'altered'))
        with self.assertRaisesRegex(ValueError, 'mismatch'):
            check(self.output)

    def test_extra_and_missing_entries_are_rejected(self):
        build(self.root, self.output)
        self.rewrite_zip(self.output, lambda entries: entries.__setitem__('extra.txt', b'undocumented'))
        with self.assertRaisesRegex(ValueError, 'members'):
            check(self.output)
        self.rewrite_zip(self.output, lambda entries: (entries.pop('extra.txt'), entries.pop('source/README.md')))
        with self.assertRaisesRegex(ValueError, 'members'):
            check(self.output)

    def test_traversal_and_duplicate_archive_names_are_rejected_without_extraction(self):
        for name in ('../escape', '/absolute', 'source/../escape', 'a\\b', 'C:drive'):
            with zipfile.ZipFile(self.output, 'w') as archive:
                archive.writestr(name, b'x')
            with self.assertRaisesRegex(ValueError, 'Unsafe'):
                check(self.output)
        with zipfile.ZipFile(self.output, 'w') as archive:
            archive.writestr('duplicate', b'a')
            with self.assertWarns(UserWarning):
                archive.writestr('duplicate', b'b')
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            check(self.output)
        self.assertFalse((self.root / 'escape').exists())

    def test_no_clobber_and_existing_lock_preserved(self):
        self.output.write_bytes(b'user data')
        with self.assertRaisesRegex(ValueError, 'already exists'):
            build(self.root, self.output)
        self.assertEqual(self.output.read_bytes(), b'user data')
        self.output.unlink()
        lock = self.root / '.jonnylean.lock'
        lock.write_text('other process')
        with self.assertRaises(FileExistsError):
            build(self.root, self.output)
        self.assertEqual(lock.read_text(), 'other process')

    def test_source_symlinks_and_source_destination_are_rejected(self):
        (self.root / 'docs/external.md').symlink_to(self.seed / 'README.md')
        with self.assertRaisesRegex(ValueError, 'Symlinked'):
            source_names(self.root)
        with self.assertRaisesRegex(ValueError, 'under artifacts'):
            build(self.root, self.root / 'source.zip')

    def test_report_changes_during_collection_are_rejected(self):
        original = readiness
        def changed(root):
            result = original(root)
            path = root / 'artifacts/JL-001/report.json'
            value = json.loads(path.read_text())
            value['findings'] = ['changed']
            path.write_bytes(encoded(value))
            return result
        with patch('tools.release.readiness', side_effect=changed), self.assertRaisesRegex(ValueError, 'Report changed'):
            collect(self.root)

    def test_whole_archive_digest_and_size_limits(self):
        build(self.root, self.output)
        with self.assertRaisesRegex(ValueError, 'supplied digest'):
            check(self.output, '0' * 64)
        with self.assertRaisesRegex(ValueError, '64 hexadecimal'):
            check(self.output, 'bad')
        with patch('tools.release.MAX_TOTAL_BYTES', 10), self.assertRaisesRegex(ValueError, 'size'):
            check(self.output)

    def test_check_cli_needs_no_project_or_lean(self):
        build(self.root, self.output)
        result = subprocess.run([sys.executable, str(PROJECT / 'tools/jonnylean.py'), 'release', 'check',
                                 str(self.output), '--project', str(self.root / 'absent')],
                                cwd=self.parent, capture_output=True, text=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['integrity'], 'pass')

    def test_path_replacement_checks_one_open_archive(self):
        first = build(self.root, self.output)
        expected_count = check(self.output)['files']
        (self.root / 'docs/additional.md').write_text('Another valid archive has one more entry.\n')
        other = self.root / 'artifacts/other.zip'
        build(self.root, other)
        original_zip = zipfile.ZipFile
        opened = []
        def replace_before_open(handle, *args, **kwargs):
            opened.append(True)
            other.replace(self.output)
            return original_zip(handle, *args, **kwargs)
        with patch('tools.release.zipfile.ZipFile', side_effect=replace_before_open):
            result = check(self.output, first['sha256'])
        self.assertEqual(opened, [True])
        self.assertEqual(result['files'], expected_count)
        self.assertEqual(result['sha256'], first['sha256'])
        self.assertNotEqual(digest(self.output.read_bytes()), first['sha256'])

    def test_in_place_archive_mutation_is_rejected(self):
        first = build(self.root, self.output)
        (self.root / 'docs/additional.md').write_text('A different valid ZIP.\n')
        other = self.root / 'artifacts/other.zip'
        build(self.root, other)
        replacement = other.read_bytes()
        original_zip = zipfile.ZipFile
        def overwrite_before_open(handle, *args, **kwargs):
            # Change the same inode after the first digest, before ZIP member checks.
            self.output.write_bytes(replacement)
            return original_zip(handle, *args, **kwargs)
        with patch('tools.release.zipfile.ZipFile', side_effect=overwrite_before_open):
            with self.assertRaisesRegex(ValueError, 'changed while checking'):
                check(self.output, first['sha256'])


if __name__ == '__main__':
    unittest.main()

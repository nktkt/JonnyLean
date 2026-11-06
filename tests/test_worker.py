"""Deterministic worker integration tests; fake reviews exist ONLY in temp dirs.

The fake executable implements the Codex structured-output/event protocol. It is
not an AI provider and its explicitly synthetic reviews are never project evidence.
"""
from __future__ import annotations
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from contextlib import redirect_stdout
from io import StringIO

PROJECT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT))
from worker.engine import Engine, DEFAULTS, snapshot, source_files
from worker.provider import CodexProvider
from worker.state import BudgetExceeded, Store, WorkerError

FAKE_PROVIDER = r'''
import json
import os
from pathlib import Path
import sys
args=sys.argv
prompt=sys.stdin.read()
out=Path(args[args.index('--output-last-message')+1])
schema=json.loads(Path(args[args.index('--output-schema')+1]).read_text())
workspace=Path(args[args.index('-C')+1])
config=json.loads((workspace.parent.parent.parent.parent/'fake-config.json').read_text())
phase='review' if 'decision' in schema['properties'] else 'generate'
if phase=='review':
    result={'decision':'approve','findings':[], 'checks':[
        {'criterion':c,'result':'pass','evidence':'SYNTHETIC TEST FIXTURE ONLY; not a real independent AI review.'}
        for c in ('definition','quantifiers','assumptions','conclusion','proof','coverage','audit')]}
    if config.get('reject_review'):
        result['decision']='changes_requested'
        result['findings']=['Synthetic reviewer deliberately requests changes.']
else:
    result={'files':config.get('files',[]),'summary':'SYNTHETIC TEST FIXTURE ONLY'}
print(json.dumps({'type':'thread.started','thread_id':'synthetic-test-thread'}),flush=True)
print(json.dumps({'type':'turn.completed','usage':{'input_tokens':100,'output_tokens':50,'cached_input_tokens':0}}),flush=True)
out.write_text(json.dumps(result))
'''


class StateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='jonnylean-state-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = Store(self.root)

    def test_concurrent_claims_have_exactly_one_owner(self):
        with ThreadPoolExecutor(max_workers=8) as pool:
            rows = list(pool.map(lambda _: Store(self.root).claim('JL-001', {}, 60, explicit=True), range(16)))
        claimed = [row for row in rows if row]
        self.assertEqual(len(claimed), 1)
        self.assertEqual(len(self.store.list()), 1)

    def test_atomic_daily_budget_reservations(self):
        limits = DEFAULTS | {'max_daily_calls': 1}
        jobs = [self.store.claim(f'JL-{index:03}', {}, 60, explicit=True) for index in range(2)]
        def reserve(job):
            try:
                return self.store.reserve(job['id'], job['owner'], 'generate', limits)
            except BudgetExceeded:
                return None
        with ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(reserve, jobs))
        self.assertEqual(sum(result is not None for result in results), 1)

    def test_unknown_usage_keeps_reservation_and_overrun_stops(self):
        job = self.store.claim('JL-001', {}, 60)
        limits = DEFAULTS | {'max_job_cost_usd': 200}
        call = self.store.reserve(job['id'], job['owner'], 'generate', limits)
        self.store.settle(call, None, {'synthetic': True}, limits)
        self.assertEqual(self.store.get(job['id'])['tokens'], DEFAULTS['max_call_tokens'])
        call = self.store.reserve(job['id'], job['owner'], 'generate', limits)
        with self.assertRaises(BudgetExceeded):
            self.store.settle(call, {'input_tokens': DEFAULTS['max_call_tokens'] + 1, 'output_tokens': 1}, {}, limits)
        self.assertEqual(self.store.get(job['id'])['tokens'], 2 * DEFAULTS['max_call_tokens'] + 2)

    def test_partial_usage_cannot_refund_reservation(self):
        job = self.store.claim('JL-001',{},60)
        call = self.store.reserve(job['id'],job['owner'],'generate',DEFAULTS)
        self.store.settle(call,{'input_tokens':10,'output_tokens':10},{'usage_complete':False},DEFAULTS)
        self.assertEqual(self.store.get(job['id'])['tokens'],DEFAULTS['max_call_tokens'])
        self.assertEqual(self.store.call_records(job['id'])[0]['state'],'partial_usage_reservation')


    def test_live_lease_cannot_resume_expired_lease_can(self):
        job = self.store.claim('JL-001', {}, 60)
        with self.assertRaises(WorkerError):
            self.store.resume(job['id'], 60)
        with self.store.transaction() as db:
            db.execute('UPDATE jobs SET lease_until=? WHERE id=?', (time.time()-1, job['id']))
        resumed = self.store.resume(job['id'], 60)
        self.assertNotEqual(resumed['owner'], job['owner'])
        self.assertEqual(resumed['started_at'], job['started_at'])


class ProviderProtocolTests(unittest.TestCase):
    def test_timeout_stops_descendants_and_does_not_forward_secret(self):
        with tempfile.TemporaryDirectory(prefix='jonnylean-provider-test-') as temp:
            root = Path(temp)
            script = root / 'fake_timeout.py'
            script.write_text("import json,os,subprocess,sys,time\n"
                              "from pathlib import Path\n"
                              "child=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)'],start_new_session=True)\n"
                              "Path('child.pid').write_text(str(child.pid))\n"
                              "print(json.dumps({'secret_forwarded':'JONNYLEAN_TEST_SECRET' in os.environ}),flush=True)\n"
                              "time.sleep(60)\n")
            original = os.environ.get('JONNYLEAN_TEST_SECRET')
            os.environ['JONNYLEAN_TEST_SECRET'] = 'synthetic secret that must not be forwarded'
            try:
                result, usage, metadata, error = CodexProvider([sys.executable,str(script)]).call(
                    root, root/'call', 'generate', 'synthetic timeout test', 0.5)
            finally:
                if original is None:
                    os.environ.pop('JONNYLEAN_TEST_SECRET',None)
                else:
                    os.environ['JONNYLEAN_TEST_SECRET']=original
            self.assertIsNone(result)
            self.assertIsNone(usage)
            self.assertIn('exceeded',error)
            self.assertLess(metadata['seconds'],5)
            self.assertFalse(json.loads((root/'call'/'events.jsonl').read_text())['secret_forwarded'])
            child=int((root/'child.pid').read_text())
            state=subprocess.run(['ps','-o','stat=','-p',str(child)],capture_output=True,text=True).stdout.strip()
            self.assertTrue(not state or state.startswith('Z'),f'descendant still running: {state}')


class WorkerIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='jonnylean-worker-tests-')
        cls.addClassCleanup(cls.temp.cleanup)
        cls.parent = Path(cls.temp.name)
        cls.seed = cls.parent / 'seed'
        cls.seed.mkdir()
        for path in source_files(PROJECT):
            relative = path.relative_to(PROJECT)
            if relative.parts[0] in ('tests', 'artifacts') or (relative.parts[0] == 'reviews' and relative.suffix == '.json'):
                continue
            destination = cls.seed / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, destination)
        cls.fake = cls.parent / 'fake_codex.py'
        cls.fake.write_text(FAKE_PROVIDER)

    def setUp(self):
        self.root = self.parent / self._testMethodName
        shutil.copytree(self.seed, self.root)
        # Real current task source + verifier, isolated fake provider protocol.
        (self.root / 'fake-config.json').write_text('{}')
        self.engine = Engine(self.root, CodexProvider([sys.executable, str(self.fake)], label='SYNTHETIC TEST FIXTURE; not an AI provider'))

    def config(self, **values):
        (self.root / 'fake-config.json').write_text(json.dumps(values))

    def test_real_verifier_fake_provider_and_safe_local_adoption(self):
        before = (self.root / 'JonnyLean/NumberTheory/Parity.lean').read_text()
        self.config(files=[{'path':'JonnyLean/NumberTheory/Parity.lean', 'content':before+'\n-- Synthetic temporary fixture change.\n'}])
        job = self.engine.create('JL-001')
        result = self.engine.run(job)
        self.assertEqual(result['state'], 'verified', result.get('error'))
        self.assertEqual((self.root / 'JonnyLean/NumberTheory/Parity.lean').read_text(), before)
        report = self.engine.write_report(job['id'])
        self.assertEqual(len(report['calls']), 2)
        self.assertEqual(report['calls'][0]['usage']['input_tokens'], 100)
        self.assertNotIn('reported_model', report['calls'][0]['metadata'])
        record = json.loads((self.engine.directory(job['id'])/'review.json').read_text())
        self.assertFalse(record['reviewer']['authenticated'])
        self.assertTrue(all('SYNTHETIC' in check['evidence'] for check in record['checks']))
        adopted = self.engine.adopt(job['id'])
        self.assertEqual(adopted['state'], 'adopted')
        self.assertIn('Synthetic temporary fixture change', (self.root/'JonnyLean/NumberTheory/Parity.lean').read_text())

    def test_protected_path_proposals_fail_three_times(self):
        before = (self.root/'jonnylean.toml').read_text()
        self.config(files=[{'path':'jonnylean.toml','content':'schema=999'}])
        job = self.engine.create('JL-001')
        result = self.engine.run(job)
        self.assertEqual(result['state'], 'failed')
        self.assertEqual(result['attempts'], 3)
        self.assertEqual(result['calls'], 3)
        self.assertIn('protected', result['error'])
        self.assertEqual((self.root/'jonnylean.toml').read_text(), before)

    def test_snapshot_prunes_state_builds_and_workspace_recursion(self):
        (self.root/'.lake').mkdir()
        (self.root/'.lake'/'bad.lean').write_text('ignore')
        (self.root/'.jonnylean'/'old.json').write_text('{}')
        job = self.engine.create('JL-001')
        workspace = self.engine.directory(job['id'])/'workspace'
        self.assertFalse((workspace/'.jonnylean').exists())
        self.assertFalse((workspace/'.lake').exists())
        self.assertEqual(snapshot(workspace), job['base'])

    def test_stale_source_blocks_verified_adoption(self):
        job = self.engine.create('JL-001')
        result = self.engine.run(job)
        self.assertEqual(result['state'], 'verified', result.get('error'))
        (self.root/'specs/JL-001.md').write_text('Source changed after proposal')
        with self.assertRaisesRegex(WorkerError, 'stale'):
            self.engine.adopt(job['id'])
        self.assertEqual(self.engine.store.get(job['id'])['state'], 'verified')

    def test_requested_adoption_failure_remains_visible_and_cli_fails(self):
        from worker import cli
        job = self.engine.create('JL-001')
        with patch.object(self.engine,'adopt',side_effect=WorkerError('Synthetic stale integration')):
            result = self.engine.run(job,adopt=True)
        self.assertEqual(result['state'],'verified',result.get('error'))
        self.assertIn('Synthetic stale integration',result['result']['integration_error'])
        regenerated = self.engine.write_report(job['id'])
        self.assertIn('Synthetic stale integration',regenerated['job']['result']['integration_error'])
        with patch('worker.cli.Engine',return_value=self.engine), patch.object(self.engine,'work',return_value=[result]), redirect_stdout(StringIO()):
            code=cli.main(self.root,['work','--task','JL-001','--adopt'])
        self.assertEqual(code,1)


    def test_resume_retains_attempts_and_budget(self):
        job = self.engine.create('JL-001')
        self.engine.store.transition(job['id'],job['owner'],'interrupted','Synthetic interruption',release=True,attempt=True)
        resumed = self.engine.resume(job['id'])
        self.assertEqual(resumed['state'], 'verified', resumed.get('error'))
        self.assertEqual(resumed['attempts'], 2)
        self.assertEqual(resumed['started_at'], job['started_at'])
        self.assertEqual(resumed['calls'], 2)

    def test_expired_wall_budget_prevents_provider_call(self):
        job = self.engine.create('JL-001')
        with self.engine.store.transaction() as db:
            db.execute('UPDATE jobs SET started_at=? WHERE id=?',(time.time()-99999,job['id']))
        result = self.engine.run(job)
        self.assertEqual(result['state'], 'budget_exhausted')
        self.assertEqual(result['calls'], 0)

    def test_protected_candidate_mutation_fails_before_provider(self):
        job = self.engine.create('JL-001')
        (self.engine.directory(job['id'])/'workspace'/'contracts/JL001.lean').write_text('bad')
        result = self.engine.run(job)
        self.assertEqual(result['state'], 'failed')
        self.assertIn('Protected source changed',result['error'])
        self.assertEqual(result['calls'], 0)

    def test_invalid_review_destinations_never_write_outside_reviews(self):
        job = self.engine.create('JL-001')
        _, task = self.engine.task('JL-001')
        workspace = self.engine.directory(job['id'])/'workspace'
        original = (workspace/'jonnylean.toml').read_bytes()
        outside = self.engine.directory(job['id'])/'outside.json'
        for destination in ('../outside.json',str(outside),'jonnylean.toml',
                            'reviews/../outside.json','reviews/./bad.json'):
            with self.assertRaises(WorkerError):
                self.engine.record_review(job,dict(task,review=destination),{}, {}, {})
        self.assertFalse(outside.exists())
        self.assertEqual((workspace/'jonnylean.toml').read_bytes(),original)
        (workspace/'reviews'/'external').symlink_to(self.engine.directory(job['id']),target_is_directory=True)
        with self.assertRaises(WorkerError):
            self.engine.record_review(job,dict(task,review='reviews/external/outside.json'),{}, {}, {})
        self.assertFalse(outside.exists())


    def test_parallel_job_workspaces_share_no_source_files(self):
        one = self.engine.create('JL-001')
        two = self.engine.create('JL-004')
        first = self.engine.directory(one['id'])/'workspace'/'JonnyLean/NumberTheory/Parity.lean'
        second = self.engine.directory(two['id'])/'workspace'/'JonnyLean/NumberTheory/Parity.lean'
        before = second.read_text()
        first.write_text(before+'\n-- isolated synthetic edit\n')
        self.assertEqual(second.read_text(),before)
        self.assertEqual((self.root/'JonnyLean/NumberTheory/Parity.lean').read_text(),before)
        self.assertNotEqual(first.stat().st_ino,second.stat().st_ino)


    def test_import_and_execution_changes_are_rejected(self):
        job = self.engine.create('JL-001')
        _,task = self.engine.task('JL-001')
        source=(self.root/'JonnyLean/NumberTheory/Parity.lean').read_text()
        for content in ('import Lean\n'+source, source+'\n#eval IO.println "bad"\n'):
            with self.assertRaises(WorkerError):
                self.engine.apply_proposal(job,task,{'files':[{'path':'JonnyLean/NumberTheory/Parity.lean','content':content}],'summary':'Synthetic unsafe attempt'})

if __name__=='__main__':
    unittest.main()

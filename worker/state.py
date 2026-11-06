"""SQLite leases and conservative budget accounting (never provider billing)."""
from __future__ import annotations

from contextlib import contextmanager, closing
from datetime import datetime
from zoneinfo import ZoneInfo
import json
from pathlib import Path
import sqlite3
import time
import uuid


class WorkerError(Exception):
    pass


class BudgetExceeded(WorkerError):
    pass


class Store:
    def __init__(self, root: Path):
        self.root = root
        self.directory = root / '.jonnylean'
        self.directory.mkdir(parents=True, exist_ok=True)
        self.path = self.directory / 'state.sqlite3'
        with closing(self.connect()) as db:
            db.executescript('''
                CREATE TABLE IF NOT EXISTS jobs (
                    id TEXT PRIMARY KEY, task TEXT NOT NULL, state TEXT NOT NULL,
                    owner TEXT, lease_until REAL, created_at REAL NOT NULL,
                    updated_at REAL NOT NULL, started_at REAL NOT NULL,
                    attempts INTEGER NOT NULL DEFAULT 0, base TEXT NOT NULL,
                    error TEXT, result TEXT, calls INTEGER NOT NULL DEFAULT 0,
                    tokens INTEGER NOT NULL DEFAULT 0, cost REAL NOT NULL DEFAULT 0
                );
                CREATE UNIQUE INDEX IF NOT EXISTS one_active_task ON jobs(task)
                    WHERE owner IS NOT NULL;
                CREATE TABLE IF NOT EXISTS history (
                    seq INTEGER PRIMARY KEY AUTOINCREMENT, job TEXT NOT NULL,
                    at REAL NOT NULL, state TEXT NOT NULL, detail TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS calls (
                    id TEXT PRIMARY KEY, job TEXT NOT NULL, day TEXT NOT NULL,
                    phase TEXT NOT NULL, state TEXT NOT NULL, reserved_tokens INTEGER NOT NULL,
                    reserved_cost REAL NOT NULL, accounted_tokens INTEGER NOT NULL,
                    accounted_cost REAL NOT NULL, usage TEXT, metadata TEXT
                );
                CREATE TABLE IF NOT EXISTS daily (
                    day TEXT PRIMARY KEY, calls INTEGER NOT NULL DEFAULT 0,
                    tokens INTEGER NOT NULL DEFAULT 0, cost REAL NOT NULL DEFAULT 0
                );
            ''')

    def connect(self):
        db = sqlite3.connect(self.path, timeout=30, isolation_level=None)
        db.row_factory = sqlite3.Row
        db.execute('PRAGMA busy_timeout=30000')
        db.execute('PRAGMA journal_mode=WAL')
        return db

    @contextmanager
    def transaction(self):
        db = self.connect()
        try:
            db.execute('BEGIN IMMEDIATE')
            yield db
            db.commit()
        except BaseException:
            db.rollback()
            raise
        finally:
            db.close()

    @staticmethod
    def decode(row):
        if row is None:
            return None
        result = dict(row)
        for key in ('base', 'result'):
            if result.get(key) is not None:
                result[key] = json.loads(result[key])
        return result

    def get(self, job_id: str):
        with closing(self.connect()) as db:
            row = db.execute('SELECT * FROM jobs WHERE id=?', (job_id,)).fetchone()
        if row is None:
            raise WorkerError(f'Unknown job: {job_id}')
        return self.decode(row)

    def list(self):
        with closing(self.connect()) as db:
            return [self.decode(row) for row in db.execute('SELECT * FROM jobs ORDER BY created_at DESC')]

    def history(self, job_id):
        with closing(self.connect()) as db:
            return [dict(row) for row in db.execute('SELECT * FROM history WHERE job=? ORDER BY seq', (job_id,))]

    def call_records(self, job_id):
        with closing(self.connect()) as db:
            rows = [dict(row) for row in db.execute('SELECT * FROM calls WHERE job=? ORDER BY rowid', (job_id,))]
        for row in rows:
            for key in ('usage', 'metadata'):
                row[key] = json.loads(row[key]) if row[key] else None
        return rows

    def claim(self, task: str, base: dict, lease: int, *, explicit: bool = False):
        now = time.time()
        owner = uuid.uuid4().hex
        with self.transaction() as db:
            stale = db.execute('SELECT id FROM jobs WHERE owner IS NOT NULL AND lease_until<?', (now,)).fetchall()
            for row in stale:
                db.execute("UPDATE jobs SET state='interrupted',owner=NULL,lease_until=NULL,updated_at=?,error=? WHERE id=?",
                           (now, 'Lease expired; resume explicitly to retain this job and budget.', row['id']))
                db.execute('INSERT INTO history(job,at,state,detail) VALUES(?,?,?,?)',
                           (row['id'], now, 'interrupted', 'Lease expired'))
            if db.execute('SELECT 1 FROM jobs WHERE task=? AND owner IS NOT NULL', (task,)).fetchone():
                return None
            # A queue never silently abandons a failed/interrupted job or repeats a
            # finished task. Explicit --task starts a new job; resume retains caps.
            if not explicit and db.execute('SELECT 1 FROM jobs WHERE task=?', (task,)).fetchone():
                return None
            job_id = 'job-' + uuid.uuid4().hex[:16]
            db.execute('INSERT INTO jobs(id,task,state,owner,lease_until,created_at,updated_at,started_at,base) VALUES(?,?,?,?,?,?,?,?,?)',
                       (job_id, task, 'claimed', owner, now + lease, now, now, now, json.dumps(base, sort_keys=True)))
            db.execute('INSERT INTO history(job,at,state,detail) VALUES(?,?,?,?)', (job_id, now, 'claimed', 'Atomic task claim'))
        return self.get(job_id)

    def resume(self, job_id: str, lease: int):
        now, owner = time.time(), uuid.uuid4().hex
        with self.transaction() as db:
            row = db.execute('SELECT * FROM jobs WHERE id=?', (job_id,)).fetchone()
            if row is None:
                raise WorkerError(f'Unknown job: {job_id}')
            if row['owner'] and row['lease_until'] >= now:
                raise WorkerError('Job has a live lease; another worker still owns it')
            if row['state'] in ('adopted', 'verified'):
                raise WorkerError(f"Job is already {row['state']}; use adopt/report")
            other = db.execute('SELECT 1 FROM jobs WHERE task=? AND owner IS NOT NULL AND id<>?', (row['task'], job_id)).fetchone()
            if other:
                raise WorkerError('Another job owns this task')
            db.execute("UPDATE jobs SET owner=?,lease_until=?,state='resuming',updated_at=? WHERE id=?", (owner, now + lease, now, job_id))
            db.execute('INSERT INTO history(job,at,state,detail) VALUES(?,?,?,?)', (job_id, now, 'resuming', 'Original attempts, start time, and budget retained'))
        return self.get(job_id)

    def heartbeat(self, job_id, owner, lease):
        with self.transaction() as db:
            cursor = db.execute('UPDATE jobs SET lease_until=?,updated_at=? WHERE id=? AND owner=? AND lease_until>=?',
                                (time.time() + lease, time.time(), job_id, owner, time.time()))
            if cursor.rowcount != 1:
                raise WorkerError('Worker lost its lease')

    def transition(self, job_id, owner, state, detail='', *, release=False, result=None, attempt=False):
        now = time.time()
        with self.transaction() as db:
            row = db.execute('SELECT owner,lease_until FROM jobs WHERE id=?', (job_id,)).fetchone()
            if row is None or row['owner'] != owner or (owner and row['lease_until'] < now):
                raise WorkerError('Worker no longer owns this job')
            db.execute('UPDATE jobs SET state=?,updated_at=?,error=?,result=COALESCE(?,result),attempts=attempts+?,owner=?,lease_until=? WHERE id=?',
                       (state, now, detail or None, json.dumps(result) if result is not None else None,
                        int(attempt), None if release else owner, None if release else row['lease_until'], job_id))
            db.execute('INSERT INTO history(job,at,state,detail) VALUES(?,?,?,?)', (job_id, now, state, detail))

    def reserve(self, job_id, owner, phase, limits):
        now = time.time()
        day = datetime.now(ZoneInfo(limits.get('budget_timezone', 'Asia/Tokyo'))).date().isoformat()
        tokens = limits['max_call_tokens']
        # Reserving every token at the higher configured rate is intentionally
        # conservative. It is a local estimate, not an invoice or quota API.
        cost = tokens * max(limits['input_usd_per_million'], limits['output_usd_per_million']) / 1_000_000
        with self.transaction() as db:
            job = db.execute('SELECT * FROM jobs WHERE id=?', (job_id,)).fetchone()
            if not job or job['owner'] != owner or job['lease_until'] < now:
                raise WorkerError('Cannot reserve budget without a live job lease')
            if now - job['started_at'] >= limits['job_timeout_seconds']:
                raise BudgetExceeded('Job wall-time budget exhausted (including time before resume)')
            db.execute('INSERT OR IGNORE INTO daily(day) VALUES(?)', (day,))
            daily = db.execute('SELECT * FROM daily WHERE day=?', (day,)).fetchone()
            for label, used, increment, cap in (
                ('job calls', job['calls'], 1, limits['max_job_calls']),
                ('job tokens', job['tokens'], tokens, limits['max_job_tokens']),
                ('job estimated USD', job['cost'], cost, limits['max_job_cost_usd']),
                ('daily calls', daily['calls'], 1, limits['max_daily_calls']),
                ('daily tokens', daily['tokens'], tokens, limits['max_daily_tokens']),
                ('daily estimated USD', daily['cost'], cost, limits['max_daily_cost_usd']),
            ):
                if used + increment > cap + 1e-9:
                    raise BudgetExceeded(f'{label} reservation would exceed limit ({used + increment:g} > {cap:g})')
            call_id = uuid.uuid4().hex
            db.execute('INSERT INTO calls(id,job,day,phase,state,reserved_tokens,reserved_cost,accounted_tokens,accounted_cost) VALUES(?,?,?,?,?,?,?,?,?)',
                       (call_id, job_id, day, phase, 'reserved', tokens, cost, tokens, cost))
            db.execute('UPDATE jobs SET calls=calls+1,tokens=tokens+?,cost=cost+? WHERE id=?', (tokens, cost, job_id))
            db.execute('UPDATE daily SET calls=calls+1,tokens=tokens+?,cost=cost+? WHERE day=?', (tokens, cost, day))
        return call_id

    def settle(self, call_id, usage, metadata, limits):
        """Use observed tokens if complete; retain the reservation otherwise."""
        with self.transaction() as db:
            call = db.execute('SELECT * FROM calls WHERE id=?', (call_id,)).fetchone()
            if not call or call['state'] != 'reserved':
                raise WorkerError('Invalid or already settled call')
            observed = (isinstance(usage, dict) and type(usage.get('input_tokens')) is int
                        and type(usage.get('output_tokens')) is int
                        and usage['input_tokens'] >= 0 and usage['output_tokens'] >= 0)
            tokens, cost = call['reserved_tokens'], call['reserved_cost']
            if observed:
                tokens = usage['input_tokens'] + usage['output_tokens']
                cost = (usage['input_tokens'] * limits['input_usd_per_million'] +
                        usage['output_tokens'] * limits['output_usd_per_million']) / 1_000_000
            complete = metadata.get('usage_complete', True)
            if observed and not complete:
                tokens = max(tokens, call['reserved_tokens'])
                cost = max(cost, call['reserved_cost'])
            accounting_state = ('observed_estimate' if complete else 'partial_usage_reservation') if observed else 'reservation_retained'
            db.execute('UPDATE calls SET state=?,accounted_tokens=?,accounted_cost=?,usage=?,metadata=? WHERE id=?',
                       (accounting_state, tokens, cost,
                        json.dumps(usage), json.dumps(metadata), call_id))
            db.execute('UPDATE jobs SET tokens=tokens+?,cost=cost+? WHERE id=?',
                       (tokens - call['reserved_tokens'], cost - call['reserved_cost'], call['job']))
            db.execute('UPDATE daily SET tokens=tokens+?,cost=cost+? WHERE day=?',
                       (tokens - call['reserved_tokens'], cost - call['reserved_cost'], call['day']))
            overrun = tokens > call['reserved_tokens'] or cost > call['reserved_cost'] + 1e-9
        if overrun:
            raise BudgetExceeded('Provider usage exceeded its local reservation; usage recorded and further work stopped')

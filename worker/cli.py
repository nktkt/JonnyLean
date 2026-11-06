"""Command-line entry points called by tools/jonnylean.py."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

from .engine import Engine, clean_environment, load_settings
from .state import WorkerError


def main(root: Path, argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog='jonnylean worker')
    parser.add_argument('command', choices=('doctor', 'status', 'work', 'resume', 'adopt', 'report'))
    parser.add_argument('job', nargs='?')
    parser.add_argument('--project', type=Path, default=root)
    parser.add_argument('--task')
    parser.add_argument('--loop', nargs='?', type=int, const=100, default=1, metavar='MAX_JOBS')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--adopt', action='store_true', help='integrate locally after both gates pass; no publication')
    args = parser.parse_args(argv)
    root = args.project.resolve()
    try:
        if args.command == 'doctor':
            limits = load_settings(root)
            checks = {'python': sys.version.split()[0], 'project': str(root), 'settings': limits,
                      'codex': shutil.which('codex'), 'lake': shutil.which('lake'),
                      'billing': 'local conservative estimates; not actual provider charges',
                      'token_limit': 'reservation plus post-call enforcement; Codex CLI does not expose a hard per-call token cap'}
            if not checks['lake'] and (Path.home() / '.elan/bin/lake').is_file():
                checks['lake'] = str(Path.home() / '.elan/bin/lake')
            for name, command in (('codex_version', ['codex', '--version']), ('authentication', ['codex', 'login', 'status'])):
                try:
                    result = subprocess.run(command, capture_output=True, text=True, timeout=15, env=clean_environment())
                    checks[name] = {'exit_code': result.returncode, 'output': (result.stdout + result.stderr).strip()}
                except (OSError, subprocess.TimeoutExpired) as exception:
                    checks[name] = {'error': str(exception)}
            print(json.dumps(checks, ensure_ascii=False, indent=2))
            return 0 if checks['codex'] and checks['lake'] and checks['authentication'].get('exit_code') == 0 else 2
        engine = Engine(root)
        if args.command == 'status':
            value = engine.store.get(args.job) if args.job else engine.store.list()
        elif args.command == 'work':
            value = engine.work(args.task, args.jobs, args.loop, args.adopt)
            if not value:
                print('No eligible tasks: queue is completed, claimed, or waiting for adopted dependencies. Use status, resume JOB, or an explicit --task.')
                return 0
        elif args.command in ('resume', 'adopt', 'report'):
            if not args.job:
                parser.error(f'{args.command} requires JOB_ID')
            if args.command == 'resume':
                value = engine.resume(args.job, args.adopt)
            elif args.command == 'adopt':
                value = engine.adopt(args.job)
            else:
                value = engine.write_report(args.job)
        print(json.dumps(value, ensure_ascii=False, indent=2))
        if args.command in ('work', 'resume'):
            rows = value if isinstance(value, list) else [value]
            accepted = ('adopted',) if args.adopt or engine.settings['auto_adopt'] else ('verified', 'adopted')
            return 0 if all(row['state'] in accepted for row in rows) else 1
        return 0
    except (WorkerError, OSError, ValueError, TypeError, KeyError) as exception:
        print(f'Worker: {exception}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main(Path.cwd(), sys.argv[1:]))

"""Read-only execution plans and deterministic CI partitioning."""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys


def expand_dependencies(tasks: list[dict], ids: list[str]) -> list[dict]:
    by_id = {t['id']: t for t in tasks}
    wanted, pending = set(), list(ids)
    while pending:
        current = pending.pop()
        if current not in by_id:
            raise ValueError(f'Unknown task dependency: {current}')
        if current not in wanted:
            wanted.add(current)
            pending.extend(by_id[current].get('depends_on', []))
    return [t for t in tasks if t['id'] in wanted]


def shard(tasks: list[dict], expression: str) -> list[dict]:
    if not re.fullmatch(r'[1-9][0-9]*/[1-9][0-9]*', expression):
        raise ValueError('Shard must be I/N with 1 <= I <= N <= 256')
    index, count = map(int, expression.split('/'))
    if not 1 <= index <= count <= 256:
        raise ValueError('Shard must be I/N with 1 <= I <= N <= 256')
    return sorted(tasks, key=lambda t: t['id'])[index - 1::count]


def levels(tasks: list[dict]) -> list[list[str]]:
    ids = {t['id'] for t in tasks}
    pending = {t['id']: set(t.get('depends_on', [])) & ids for t in tasks}
    result = []
    while pending:
        ready = sorted(name for name, deps in pending.items() if not deps)
        if not ready:
            raise ValueError('Cyclic task dependencies')
        result.append(ready)
        done = set(ready)
        pending = {name: deps - done for name, deps in pending.items() if name not in done}
    return result


def make_plan(tasks: list[dict], selected: list[dict], with_dependencies=False, partition=None) -> dict:
    wanted = {t['id'] for t in selected}
    closure = expand_dependencies(tasks, sorted(wanted))
    expanded = closure if with_dependencies else selected
    chosen = shard(expanded, partition) if partition else sorted(expanded, key=lambda t: t['id'])
    chosen_ids = {t['id'] for t in chosen}
    prerequisites = {dependency for t in chosen for dependency in t.get('depends_on', [])} - chosen_ids
    return {'schema': 1, 'requested': sorted(wanted), 'tasks': [t['id'] for t in chosen],
            'added_dependencies': sorted({t['id'] for t in expanded} - wanted),
            'prerequisites_outside_selection': sorted(prerequisites), 'layers': levels(chosen),
            'domains': dict(sorted(Counter(t.get('domain', 'unclassified') for t in chosen).items())),
            'shard': partition, 'mechanical_scope': 'whole_library',
            'contract_scope': 'selected_tasks',
            'note': 'A plan performs no verification, AI calls, reservations, or adoption. '
                    'Worker prerequisites require adopted jobs; verification compiles imports directly.'}


def main(default_root: Path, argv: list[str]) -> int:
    from tools.catalog import registry, select, affected, changed_paths
    from tools.jonnylean import OperationError
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('task', nargs='?', default='all')
    parser.add_argument('--project', type=Path, default=default_root)
    parser.add_argument('--domain')
    parser.add_argument('--tag')
    parser.add_argument('--changed', metavar='GIT_REF')
    parser.add_argument('--include-dependencies', action='store_true')
    parser.add_argument('--shard', metavar='I/N')
    parser.add_argument('--format', choices=('json', 'text'), default='text')
    args = parser.parse_args(argv)
    try:
        root = args.project.resolve()
        tasks = registry(root)
        if args.task != 'all' and args.task not in {t['id'] for t in tasks}:
            raise ValueError(f'Unknown task: {args.task}')
        chosen = select(tasks, domain=args.domain, tag=args.tag)
        if args.task != 'all':
            chosen = [t for t in chosen if t['id'] == args.task]
        if args.changed:
            chosen = affected(root, chosen, changed_paths(root, args.changed))
        plan = make_plan(tasks, chosen, args.include_dependencies, args.shard)
        if args.format == 'json':
            print(json.dumps(plan, ensure_ascii=False, indent=2))
        else:
            print(f"Plan: {len(plan['tasks'])} tasks in {len(plan['layers'])} dependency layers")
            for index, layer in enumerate(plan['layers'], 1):
                print(f"  {index}: {', '.join(layer)}")
            if plan['prerequisites_outside_selection']:
                print('Prerequisites outside selection: ' + ', '.join(plan['prerequisites_outside_selection']))
            print(plan['note'])
        return 0
    except (OperationError, OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 2

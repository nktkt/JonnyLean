"""Search and export types from a current, completed Lean declaration audit."""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sys


def current_declarations(root: Path) -> list[dict]:
    from tools.jonnylean import capture_verification_inputs
    current = capture_verification_inputs(root)
    for path in sorted((root / 'artifacts').glob('JL-*/report.json')):
        try:
            report = json.loads(path.read_text())
            if (not isinstance(report, dict) or report.get('mechanical') != 'pass'
                or report.get('verification_inputs') != current):
                continue
            rows = report['audit']['declarations']
            if (not isinstance(rows, list) or not rows or any(not isinstance(r, dict)
                or any(not isinstance(r.get(k), str) for k in ('name', 'module', 'kind', 'type'))
                or not isinstance(r.get('axioms'), list) or any(not isinstance(a, str) for a in r['axioms']) for r in rows)):
                continue
            return sorted(rows, key=lambda r: (r['module'], r['name']))
        except (OSError, ValueError, KeyError, TypeError):
            continue
    raise ValueError('No current complete declaration audit. Run verify or run first.')


def search(rows: list[dict], query=None, module=None, kind=None) -> list[dict]:
    words = (query or '').casefold().split()
    return [row for row in rows
            if (not module or row['module'] == module or row['module'].startswith(module + '.'))
            and (not kind or row['kind'] == kind)
            and all(word in (row['name'] + ' ' + row['type']).casefold() for word in words)]


def main(default_root: Path, argv: list[str]) -> int:
    from tools.jonnylean import OperationError
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('search', 'show', 'stats', 'export'))
    parser.add_argument('query', nargs='?')
    parser.add_argument('--project', type=Path, default=default_root)
    parser.add_argument('--module')
    parser.add_argument('--kind', choices=('theorem', 'definition', 'inductive', 'constructor', 'recursor', 'opaque'))
    parser.add_argument('--format', choices=('json', 'text', 'markdown'), default='text')
    args = parser.parse_args(argv)
    try:
        rows = current_declarations(args.project.resolve())
        selected = search(rows, args.query if args.action == 'search' else None, args.module, args.kind)
        if args.action == 'show':
            selected = [r for r in selected if r['name'] == args.query]
            if not selected:
                raise ValueError('Unknown declaration')
        if args.action == 'stats':
            print(json.dumps({'declarations': len(selected),
                              'kinds': dict(sorted(Counter(r['kind'] for r in selected).items())),
                              'modules': dict(sorted(Counter(r['module'] for r in selected).items())),
                              'includes_generated_declarations': True}, ensure_ascii=False, indent=2))
        elif args.format == 'json' or args.action == 'export' and args.format == 'text':
            print(json.dumps(selected, ensure_ascii=False, indent=2))
        elif args.format == 'markdown':
            print('# Audited Lean declarations\n\nIncludes compiler-generated declarations. This export does not perform a new verification.\n')
            for row in selected:
                print(f"## {row['name']}\n\nModule: `{row['module']}` · Kind: {row['kind']}\n")
                # Fence size must exceed any backtick run in an audited type.
                import re
                fence = '`' * max(3, max((len(m[0]) + 1 for m in re.finditer(r'`+', row['type'])), default=0))
                print(f"{fence}lean\n{row['type']}\n{fence}\n\nAxioms: {', '.join(row['axioms']) or 'none'}\n")
        else:
            for row in selected:
                print(f"{row['name']} [{row['kind']}]\n  {row['type']}\n  module: {row['module']}; axioms: {', '.join(row['axioms']) or 'none'}")
            print(f'{len(selected)} declarations (includes generated declarations).')
        return 0
    except (OperationError, OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 2

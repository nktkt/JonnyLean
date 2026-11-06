"""Reproducible source/evidence bundles; integrity checking never executes Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys
import tempfile
import zipfile

MAX_FILES = 20000
MAX_FILE_BYTES = 64 * 1024 * 1024
MAX_TOTAL_BYTES = 512 * 1024 * 1024
SOURCE_DIRS = ('JonnyLean', 'contracts', 'specs', 'reviews', 'catalog', 'tools',
               'tests', 'worker', 'docs', 'roadmaps', '.github')
SOURCE_EXTENSIONS = {'.lean', '.py', '.json', '.md', '.toml', '.yml', '.yaml', '.txt'}
SOURCE_FILES = ('JonnyLean.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                'jonnylean.toml', 'worker.toml', 'README.md', 'CONTRIBUTING.md',
                'LICENSE', '.gitignore')


def encoded(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_digest(path: Path) -> str:
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def safe_name(name: str) -> bool:
    return (isinstance(name, str) and bool(name) and '\\' not in name and ':' not in name
            and not any(ord(c) < 32 for c in name) and not name.startswith('/')
            and all(p not in ('', '.', '..') for p in name.split('/')))


def source_file(root: Path, name: str) -> Path:
    if not safe_name(name):
        raise ValueError(f'Invalid project path: {name}')
    path = root / name
    if (any(root.joinpath(*PurePosixPath(name).parts[:i]).is_symlink()
            for i in range(1, len(PurePosixPath(name).parts) + 1))
            or not path.resolve().is_relative_to(root) or not path.is_file()):
        raise ValueError(f'Missing, external, or symlinked file: {name}')
    return path


def source_names(root: Path) -> list[str]:
    names = {name for name in SOURCE_FILES if (root / name).exists()}
    for folder in SOURCE_DIRS:
        directory = root / folder
        if directory.is_symlink():
            raise ValueError(f'Symlinked source directory: {folder}')
        for path in directory.rglob('*'):
            if path.is_symlink():
                raise ValueError(f'Symlinked source path: {path.relative_to(root)}')
            if path.is_file() and path.suffix in SOURCE_EXTENSIONS:
                names.add(path.relative_to(root).as_posix())
    return sorted(names)


def readiness(root: Path) -> dict:
    """Check current local evidence, without changing files or invoking a prover."""
    from tools.catalog import registry, generated
    from tools.jonnylean import capture_inputs, capture_verification_inputs, check_review, OperationError, Rejected
    tasks = registry(root)
    manifest, imports, _ = generated(root)
    if ((root / 'jonnylean.toml').read_text() != manifest
            or (root / 'JonnyLean.lean').read_text() != imports):
        raise ValueError('Catalog/root imports out of date; run catalog sync')
    inputs = capture_verification_inputs(root)
    result = []
    for task in tasks:
        reasons = []
        report_hash = None
        try:
            raw = source_file(root, f'artifacts/{task["id"]}/report.json').read_bytes()
            report_hash = digest(raw)
            report = json.loads(raw)
            if not isinstance(report, dict):
                raise ValueError('Malformed report')
            if report.get('task') != task['id'] or report.get('status') != 'pass' or report.get('mechanical') != 'pass':
                reasons.append('No successful mechanical report for this task')
            if report.get('verification_inputs') != inputs:
                reasons.append('Whole-library verification is stale')
            scoped = capture_inputs(root, task)
            if report.get('inputs') != scoped:
                reasons.append('Task evidence is stale')
            check_review(root, task, {'inputs': scoped})
            if report.get('findings') != []:
                reasons.append('Report has findings or lacks a findings list')
            if not isinstance(report.get('audit'), dict) or not report['audit'].get('declarations'):
                reasons.append('Missing declaration audit')
            if not isinstance(report.get('contract_audit'), dict) or not report['contract_audit'].get('declarations'):
                reasons.append('Missing contract audit')
            if not isinstance(report.get('target'), dict) or report['target'].get('name') != task['declaration']:
                reasons.append('Target does not match the task declaration')
        except (OSError, ValueError, KeyError, TypeError, OperationError, Rejected) as error:
            reasons.append(str(error))
        result.append({'task': task['id'], 'ready': not reasons, 'reasons': reasons,
                       'report_sha256': report_hash})
    stable = inputs == capture_verification_inputs(root)
    return {'schema': 1, 'ready': stable and all(r['ready'] for r in result),
            'inputs_stable': stable, 'tasks': result, 'verification_inputs': inputs,
            'fresh_verification_performed': False, 'authenticated': False,
            'note': 'Uses current local evidence. No new Lean verification or authenticated approval.'}


def collect(root: Path) -> tuple[dict[str, bytes], dict]:
    from tools.catalog import registry
    from tools.jonnylean import capture_verification_inputs
    state = readiness(root)
    if not state['ready']:
        blocked = ', '.join(r['task'] for r in state['tasks'] if not r['ready'])
        raise ValueError('Release requires current mechanical checks and reviews: ' + (blocked or 'inputs changed'))
    names = source_names(root)
    entries = {'source/' + name: source_file(root, name).read_bytes() for name in names}
    # These hashes bind the captured bytes, not merely a later filesystem read.
    for name, expected in state['verification_inputs'].items():
        if digest(entries.get('source/' + name, b'')) != expected:
            raise ValueError(f'Captured verification input differs: {name}')
    tasks = registry(root)
    checked_reports = {row['task']: row['report_sha256'] for row in state['tasks']}
    audit = None
    for task in tasks:
        raw = source_file(root, f'artifacts/{task["id"]}/report.json').read_bytes()
        if digest(raw) != checked_reports[task['id']]:
            raise ValueError(f'Report changed during release: {task["id"]}')
        report = json.loads(raw)
        if (report.get('verification_inputs') != state['verification_inputs']
                or report.get('status') != 'pass' or report.get('mechanical') != 'pass'):
            raise ValueError(f'Report changed during release: {task["id"]}')
        # Recheck against exactly the review and source bytes captured above.
        from tools.jonnylean import capture_inputs, check_review
        if report.get('inputs') != capture_inputs(root, task):
            raise ValueError(f'Task changed during release: {task["id"]}')
        check_review(root, task, report)
        current_audit = encoded(report['audit'])
        if audit is None:
            audit = current_audit
        elif audit != current_audit:
            raise ValueError('Reports disagree on the whole-library audit')
        scope_data = encoded(report['inputs'])
        scope_name = f'evidence/scopes/{digest(scope_data)}.json'
        entries[scope_name] = scope_data
        entries[f'evidence/tasks/{task["id"]}.json'] = encoded({
            'schema': 1, 'task': task['id'], 'mechanical': report['mechanical'],
            'review': report['review'], 'human_approval': 'not_recorded',
            'target': report['target'], 'contract_audit': report['contract_audit'],
            'scope': scope_name, 'library_audit': 'evidence/library-audit.json'})
    entries['evidence/library-audit.json'] = audit
    entries['evidence/verification-inputs.json'] = encoded(state['verification_inputs'])
    entries['BUNDLE-README.txt'] = (
        'JonnyLean source and recorded evidence\n\n'
        'The source/ directory is a complete project. With the pinned Lean toolchain, run:\n'
        '  cd source\n  python3 tools/jonnylean.py run all --jobs 4\n\n'
        'Evidence is deduplicated: one library audit, per-task contracts and targets,\n'
        'and content-addressed review scopes. Original AI review records are in source/reviews/.\n'
        'This archive does not contain build outputs, AI job history, credentials, or a .git directory.\n'
        'Its manifest checks byte integrity, not author identity, mathematical correctness,\n'
        'or human approval. Re-run Lean to verify the included source.\n').encode()
    if (source_names(root) != names or state['verification_inputs'] != capture_verification_inputs(root)
            or any(entries['source/' + name] != source_file(root, name).read_bytes() for name in names)):
        raise ValueError('Project changed while collecting the release')
    summary = {'tasks': len(tasks), 'modules': len(json.loads(audit)['modules']),
               'declarations': len(json.loads(audit)['declarations'])}
    return entries, summary


def build(root: Path, destination: Path) -> dict:
    root, destination = root.resolve(), destination.absolute()
    if destination.exists() or destination.is_symlink():
        raise ValueError('Release destination already exists; choose a new filename')
    if not destination.parent.is_dir():
        raise ValueError('Release destination directory must already exist')
    # Never create a source file or lock underneath the set being packaged.
    if destination.resolve().is_relative_to(root) and destination.resolve().relative_to(root).parts[0] != 'artifacts':
        raise ValueError('Inside the project, releases must be written under artifacts/')
    lock = root / '.jonnylean.lock'
    with lock.open('x') as stream:
        stream.write(str(os.getpid()))
    temporary = None
    try:
        entries, summary = collect(root)
        if len(entries) > MAX_FILES or any(len(data) > MAX_FILE_BYTES for data in entries.values()) or sum(map(len, entries.values())) > MAX_TOTAL_BYTES:
            raise ValueError('Release exceeds supported size limits')
        manifest = {'schema': 1, 'format': 'jonnylean-release', 'summary': summary,
                    'authenticated': False, 'fresh_verification_performed': False,
                    'files': {name: {'sha256': digest(data), 'bytes': len(data)} for name, data in sorted(entries.items())}}
        entries['manifest.json'] = encoded(manifest)
        with tempfile.NamedTemporaryFile(dir=destination.parent, prefix='.jonnylean-release-', suffix='.tmp', delete=False) as stream:
            temporary = Path(stream.name)
        with zipfile.ZipFile(temporary, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for name, data in sorted(entries.items()):
                info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                archive.writestr(info, data, compresslevel=9)
        check(temporary)
        # Atomic no-clobber publish, including when another process races us.
        os.link(temporary, destination)
        return {'archive': str(destination), 'sha256': file_digest(destination), **summary}
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
        lock.unlink(missing_ok=True)


def check(path: Path, expected_sha256: str | None = None) -> dict:
    if expected_sha256 is not None and not re.fullmatch('[0-9a-fA-F]{64}', expected_sha256):
        raise ValueError('Expected SHA-256 must contain exactly 64 hexadecimal digits')
    # Pin one descriptor: renaming the path cannot swap the object being checked.
    with path.open('rb') as raw:
        actual = hashlib.file_digest(raw, 'sha256').hexdigest()
        if expected_sha256 and actual != expected_sha256.lower():
            raise ValueError('Archive SHA-256 differs from the supplied digest')
        raw.seek(0)
        with zipfile.ZipFile(raw) as archive:
            infos = archive.infolist()
            names = [i.filename for i in infos]
            if (len(infos) > MAX_FILES + 1 or len(set(names)) != len(names)
                    or any(not safe_name(n) for n in names)):
                raise ValueError('Unsafe, duplicate, or excessive archive entries')
            if ('manifest.json' not in names or any(i.is_dir() or stat.S_ISLNK(i.external_attr >> 16)
                    or i.flag_bits & 1 or i.compress_type not in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED)
                    or i.file_size > MAX_FILE_BYTES for i in infos)
                    or sum(i.file_size for i in infos) > MAX_TOTAL_BYTES):
                raise ValueError('Unsupported archive contents or size')
            manifest = json.loads(archive.read('manifest.json'))
            if (not isinstance(manifest, dict) or manifest.get('schema') != 1
                    or manifest.get('format') != 'jonnylean-release' or not isinstance(manifest.get('files'), dict)):
                raise ValueError('Unsupported release manifest')
            files = manifest['files']
            if set(files) != set(names) - {'manifest.json'}:
                raise ValueError('Archive members do not match the manifest')
            if not files:
                raise ValueError('Empty release manifest')
            for name, metadata in files.items():
                if (not isinstance(metadata, dict) or type(metadata.get('bytes')) is not int
                        or not isinstance(metadata.get('sha256'), str)
                        or not re.fullmatch('[0-9a-f]{64}', metadata['sha256'])):
                    raise ValueError(f'Invalid file metadata: {name}')
                info = archive.getinfo(name)
                if info.file_size != metadata['bytes']:
                    raise ValueError(f'File size mismatch: {name}')
                with archive.open(info) as stream:
                    measured = hashlib.file_digest(stream, 'sha256').hexdigest()
                if measured != metadata['sha256']:
                    raise ValueError(f'File digest mismatch: {name}')
        raw.seek(0)
        if hashlib.file_digest(raw, 'sha256').hexdigest() != actual:
            raise ValueError('Archive changed while checking integrity')
    return {'integrity': 'pass', 'files': len(files), 'sha256': actual,
            'expected_digest_matched': expected_sha256 is not None,
            'authenticated': False, 'fresh_verification_performed': False,
            'note': 'Checks archive byte integrity only; does not execute code, prove theorems, or authenticate the manifest.'}


def main(default_root: Path, argv: list[str]) -> int:
    from tools.jonnylean import OperationError, Rejected
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('status', 'build', 'check'))
    parser.add_argument('archive', nargs='?', type=Path)
    parser.add_argument('--project', type=Path, default=default_root)
    parser.add_argument('--sha256', help='independently supplied whole-archive digest for check')
    args = parser.parse_args(argv)
    try:
        if args.sha256 and args.action != 'check':
            raise ValueError('--sha256 is only supported by release check')
        if args.action == 'status':
            if args.archive:
                raise ValueError('release status does not take an archive')
            result = readiness(args.project.resolve())
            result.pop('verification_inputs')
            code = 0 if result['ready'] else 1
        else:
            if not args.archive:
                raise ValueError('An archive filename is required')
            result = check(args.archive, args.sha256) if args.action == 'check' else build(args.project, args.archive)
            code = 0
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return code
    except (OSError, ValueError, TypeError, KeyError, zipfile.BadZipFile, OperationError, Rejected) as error:
        print(str(error), file=sys.stderr)
        return 2

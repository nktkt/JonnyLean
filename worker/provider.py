"""Read-only Codex CLI calls with structured proposals and recorded JSON events."""
from __future__ import annotations

import json
import os
from pathlib import Path
import signal
import subprocess
import time

from .processes import clean_environment, kill_process_tree

CRITERIA = ('definition', 'quantifiers', 'assumptions', 'conclusion', 'proof', 'coverage', 'audit')

PROPOSAL_SCHEMA = {
    'type': 'object', 'additionalProperties': False, 'required': ['files', 'summary'],
    'properties': {
        'files': {'type': 'array', 'items': {
            'type': 'object', 'additionalProperties': False, 'required': ['path', 'content'],
            'properties': {'path': {'type': 'string'}, 'content': {'type': 'string'}}}},
        'summary': {'type': 'string'},
    },
}
REVIEW_SCHEMA = {
    'type': 'object', 'additionalProperties': False,
    'required': ['decision', 'findings', 'checks'],
    'properties': {
        'decision': {'type': 'string', 'enum': ['approve', 'changes_requested']},
        'findings': {'type': 'array', 'items': {'type': 'string'}},
        'checks': {'type': 'array', 'items': {
            'type': 'object', 'additionalProperties': False,
            'required': ['criterion', 'result', 'evidence'],
            'properties': {
                'criterion': {'type': 'string', 'enum': list(CRITERIA)},
                'result': {'type': 'string', 'enum': ['pass', 'fail']},
                'evidence': {'type': 'string'},
            },
        }},
    },
}


class CodexProvider:
    def __init__(self, command=None, *, label='codex-cli'):
        self.command = command or ['codex']
        self.label = label

    def call(self, workspace: Path, directory: Path, phase: str, prompt: str, timeout: float):
        directory.mkdir(parents=True, exist_ok=True)
        schema = directory / 'schema.json'
        result_file = directory / 'result.json'
        schema.write_text(json.dumps(REVIEW_SCHEMA if phase == 'review' else PROPOSAL_SCHEMA))
        (directory / 'prompt.txt').write_text(prompt)
        command = self.command + ['exec', '--ephemeral', '--json', '--sandbox', 'read-only',
                                 '-C', str(workspace), '--skip-git-repo-check',
                                 '--output-schema', str(schema), '--output-last-message', str(result_file), '-']
        started = time.monotonic()
        metadata = {'provider': self.label, 'command': command, 'fresh_context': True,
                    'sandbox': 'read-only', 'billing': 'local estimate; not actual provider charges'}
        usage, result, error = None, None, None
        events_path = directory / 'events.jsonl'
        try:
            with events_path.open('w') as out, (directory / 'stderr.txt').open('w') as err:
                process = subprocess.Popen(command, cwd=workspace, stdin=subprocess.PIPE,
                                           stdout=out, stderr=err, text=True, start_new_session=True, env=clean_environment())
                try:
                    process.communicate(input=prompt, timeout=timeout)
                except BaseException as exception:
                    # Also kill descendants on Ctrl-C or worker shutdown.
                    kill_process_tree(process)
                    process.communicate()
                    if isinstance(exception, subprocess.TimeoutExpired):
                        error = f'Codex call exceeded {timeout:.1f}s'
                    else:
                        raise
                metadata['exit_code'] = process.returncode
            if process.returncode and error is None:
                error = f'Codex exited with status {process.returncode}; see {directory / "stderr.txt"}'
        except OSError as exception:
            error = f'Cannot launch Codex CLI: {exception}'
        metadata['seconds'] = round(time.monotonic() - started, 3)
        totals = {'input_tokens': 0, 'output_tokens': 0, 'cached_input_tokens': 0}
        usage_seen = False
        last_event_type = None
        if events_path.exists():
            for line in events_path.read_text().splitlines():
                try:
                    event = json.loads(line)
                except ValueError:
                    continue
                if not isinstance(event, dict):
                    continue
                last_event_type = event.get('type')
                if isinstance(event.get('model'), str):
                    metadata['reported_model'] = event['model']
                if isinstance(event.get('thread_id'), str):
                    metadata['reported_thread_id'] = event['thread_id']
                data = event.get('usage')
                if event.get('type') == 'turn.completed' and isinstance(data, dict):
                    if all(type(data.get(key)) is int and data[key] >= 0 for key in ('input_tokens', 'output_tokens')):
                        usage_seen = True
                        for key in totals:
                            totals[key] += data.get(key, 0) if type(data.get(key, 0)) is int else 0
            if usage_seen:
                usage = totals
        if error is None:
            try:
                result = json.loads(result_file.read_text())
                if not isinstance(result, dict):
                    raise ValueError('Expected structured object')
            except (OSError, ValueError) as exception:
                error = f'Invalid structured Codex response: {exception}'
        metadata['usage_complete'] = error is None and usage_seen and last_event_type == 'turn.completed'
        return result, usage, metadata, error

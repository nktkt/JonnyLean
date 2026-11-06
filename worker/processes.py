"""Subprocess hygiene for local trusted tools (not an OS security sandbox)."""
from __future__ import annotations
import os
import signal
import subprocess


def clean_environment():
    names = ('PATH', 'HOME', 'USER', 'LOGNAME', 'LANG', 'LC_ALL', 'TERM', 'TMPDIR',
             'ELAN_HOME', 'LEAN_SYSROOT', 'CODEX_HOME', 'SSL_CERT_FILE', 'SSL_CERT_DIR')
    return {name: os.environ[name] for name in names if name in os.environ}


def kill_process_tree(process):
    """Also stop Lean subprocesses whose verifier starts new sessions."""
    descendants = [process.pid]
    try:
        result = subprocess.run(['ps', '-axo', 'pid=,ppid='], capture_output=True,
                                text=True, timeout=3, env=clean_environment())
        rows = [tuple(map(int, line.split())) for line in result.stdout.splitlines() if len(line.split()) == 2]
        for parent in descendants:
            descendants.extend(pid for pid, ppid in rows if ppid == parent and pid not in descendants)
    except (OSError, ValueError, subprocess.TimeoutExpired):
        pass
    for pid in reversed(descendants):
        try:
            os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        try:
            os.kill(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass

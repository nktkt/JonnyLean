"""Prepare a verified PR description; publish only with explicit --publish."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib


def invoke(root: Path, argv: list[str]) -> str:
    result = subprocess.run(argv, cwd=root, text=True, capture_output=True, timeout=180)
    if result.returncode:
        raise RuntimeError(f"Command failed: {' '.join(argv)}\n{result.stderr.strip()}")
    return result.stdout.strip()


def prepare(root: Path) -> tuple[Path, str]:
    from tools.jonnylean import capture_inputs, check_review, OperationError, Rejected
    config = tomllib.loads((root / "jonnylean.toml").read_text())
    lines = ["JonnyLeanの数学ライブラリと検証・独立AIレビューを更新します。", "",
             "| 課題 | 命題 | 公理依存 |", "| --- | --- | --- |"]
    for task in config["tasks"]:
        report = json.loads((root / "artifacts" / task["id"] / "report.json").read_text())
        if report.get("status") != "pass" or report.get("inputs") != capture_inputs(root, task):
            raise RuntimeError(f"{task['id']}: run all must pass on the current files before preparing a PR")
        try:
            check_review(root, task, report)
        except (OperationError, Rejected) as error:
            raise RuntimeError(f"{task['id']}: {error}") from error
        axioms = ", ".join(report["target"]["axioms"]) or "なし"
        lines.append(f"| {task['id']} | `{task['declaration']}` | {axioms} |")
    lines.extend(["", "検証: `python3 tools/jonnylean.py run all` が現在の入力に対して合格。",
                  "機械検証とAIレビューは別々に記録しています。人間の承認はこの結果には含みません。", ""])
    directory = root / "artifacts" / "pull-request"
    directory.mkdir(parents=True, exist_ok=True)
    body = directory / "body.md"
    body.write_text("\n".join(lines))
    title = f"JonnyLean: {len(config['tasks'])} verified mathematics tasks"
    (directory / "title.txt").write_text(title + "\n")
    return body, title


def publish(root: Path, body: Path, title: str, repo: str, base: str) -> str:
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9][A-Za-z0-9_.-]*", repo):
        raise RuntimeError("--repo must be owner/repository")
    invoke(root, ["git", "check-ref-format", "--branch", base])
    if invoke(root, ["git", "status", "--porcelain"]):
        raise RuntimeError("Commit reviewed changes before publishing; the working tree must be clean")
    branch = invoke(root, ["git", "branch", "--show-current"])
    if not branch.startswith("codex/") or branch == base:
        raise RuntimeError("Publish from a codex/ feature branch, separate from the base branch")
    remote = invoke(root, ["git", "remote", "get-url", "origin"])
    allowed = {f"https://github.com/{repo}.git", f"https://github.com/{repo}",
               f"git@github.com:{repo}.git", f"git@github.com:{repo}"}
    if remote not in allowed:
        raise RuntimeError("origin does not match the explicitly selected GitHub repository")
    invoke(root, ["gh", "auth", "status"])
    invoke(root, ["git", "fetch", "origin", base])
    changes = invoke(root, ["git", "diff", "--name-only", f"origin/{base}...HEAD"])
    if not changes:
        raise RuntimeError("No committed changes relative to the base branch")
    invoke(root, ["git", "push", "--set-upstream", "origin", branch])
    existing = invoke(root, ["gh", "pr", "list", "--repo", repo, "--head", branch,
                             "--base", base, "--state", "open", "--json", "url"])
    prs = json.loads(existing)
    if prs:
        return prs[0]["url"]
    return invoke(root, ["gh", "pr", "create", "--draft", "--repo", repo, "--base", base,
                         "--head", branch, "--title", title, "--body-file", str(body)])


def main(default_root: Path, argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=default_root)
    parser.add_argument("--publish", action="store_true", help="Push committed changes and create a draft PR")
    parser.add_argument("--repo", help="Explicit GitHub owner/repository; required to publish")
    parser.add_argument("--base", default="main")
    args = parser.parse_args(argv)
    root = args.project.resolve()
    try:
        invoke(root, [sys.executable, str(default_root / "tools/jonnylean.py"), "run", "all",
                      "--project", str(root)])
        body, title = prepare(root)
        print(f"Prepared: {body}")
        if args.publish:
            if not args.repo:
                raise RuntimeError("--publish requires --repo owner/repository")
            print(publish(root, body, title, args.repo, args.base))
        return 0
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(str(error), file=sys.stderr)
        return 2

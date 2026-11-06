#!/usr/bin/env python3
"""JonnyLean verification, independent review, and worker command line.

Python 3.11+ and the pinned Lean toolchain are the only runtime prerequisites.
Review records are explicit evidence, not authenticated approvals.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import tomllib

CRITERIA = {"definition", "quantifiers", "assumptions", "conclusion", "proof", "coverage", "audit"}
MARKER = "JONNYLEAN_AUDIT="


class Rejected(Exception):
    """A completed check found a policy or review failure."""


class OperationError(Exception):
    """The check could not be completed."""


def local_file(root: Path, name: str) -> Path:
    if not isinstance(name, str) or not name or Path(name).is_absolute():
        raise OperationError(f"Expected a project-relative file: {name!r}")
    path = root / name
    if not path.resolve().is_relative_to(root) or path.is_symlink() or not path.is_file():
        raise OperationError(f"Missing or external project file: {name}")
    return path


def load_task(root: Path, task_id: str) -> tuple[dict, dict]:
    data = tomllib.loads(local_file(root, "jonnylean.toml").read_text())
    if data.get("schema") != 1:
        raise OperationError("Unsupported task schema")
    timeout = data.get("timeout_seconds")
    if type(timeout) is not int or not 1 <= timeout <= 3600:
        raise OperationError("timeout_seconds must be an integer between 1 and 3600")
    allowed = data.get("allowed_axioms")
    if not isinstance(allowed, list) or any(not isinstance(a, str) for a in allowed):
        raise OperationError("allowed_axioms must be a string list")
    if "sorryAx" in allowed:
        raise OperationError("sorryAx can never be permitted")
    tasks = data.get("tasks", [])
    if not isinstance(tasks, list) or any(not isinstance(t, dict) for t in tasks):
        raise OperationError("tasks must be an array of tables")
    ids = [t.get("id") for t in tasks]
    if any(not isinstance(i, str) or not re.fullmatch(r"JL-\d{3}", i) for i in ids):
        raise OperationError("Task IDs must have the form JL-001")
    if len(ids) != len(set(ids)):
        raise OperationError("Duplicate task ID")
    declarations = [t.get("declaration") for t in tasks]
    if any(not isinstance(d, str) or not d for d in declarations) or len(set(declarations)) != len(declarations):
        raise OperationError("Task declarations must be unique nonempty strings")
    for candidate in tasks:
        review_path = candidate.get("review")
        parts = Path(review_path).parts if isinstance(review_path, str) else ()
        if (len(parts) < 2 or parts[0] != "reviews" or ".." in parts or
            not review_path.endswith(".json") or Path(review_path).is_absolute()):
            raise OperationError("Review records must be JSON files inside reviews/")
        destination = root / review_path
        if (not destination.resolve().is_relative_to(root) or
            any(root.joinpath(*parts[:i]).is_symlink() for i in range(1, len(parts) + 1))):
            raise OperationError("Review paths must not traverse symlinks or leave the project")
        dependencies = candidate.get("depends_on", [])
        if (not isinstance(dependencies, list) or
            any(not isinstance(d, str) or d not in ids or d == candidate["id"] for d in dependencies)):
            raise OperationError("Invalid task dependencies")
        editable = candidate.get("editable", [])
        if not isinstance(editable, list) or any(not isinstance(p, str) for p in editable):
            raise OperationError("Editable paths must be a list of project-relative paths")
        for path in editable:
            parts = Path(path).parts if isinstance(path, str) else ()
            if (not parts or parts[0] != "JonnyLean" or ".." in parts or not path.endswith(".lean")):
                raise OperationError("Editable paths must be Lean files inside JonnyLean/")
    def visit(item: str, ancestors: set[str]) -> None:
        if item in ancestors:
            raise OperationError("Cyclic task dependencies")
        entry = next(t for t in tasks if t["id"] == item)
        for dependency in entry.get("depends_on", []):
            visit(dependency, ancestors | {item})
    for item in ids:
        visit(item, set())
    task = next((t for t in tasks if t["id"] == task_id), None)
    if task is None:
        raise OperationError(f"Unknown task: {task_id}")
    for key in ("title", "module", "declaration", "spec", "contract", "review"):
        if not isinstance(task.get(key), str) or not task[key]:
            raise OperationError(f"Missing task field: {key}")
    for key in ("spec", "contract"):
        local_file(root, task[key])
    return data, task


def capture_inputs(root: Path, task: dict) -> dict[str, str]:
    names = {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "jonnylean.toml",
             "JonnyLean.lean", "tools/Audit.lean", "reviews/rubric.md", task["spec"], task["contract"]}
    for pattern in ("JonnyLean/**/*.lean", "contracts/**/*.lean", "specs/**/*.md", "tools/*.py",
                    "tests/**/*.py", "worker/**/*.py", "worker.toml", ".github/workflows/*"):
        names.update(str(p.relative_to(root)) for p in root.glob(pattern) if p.is_file())
    return {name: hashlib.sha256(local_file(root, name).read_bytes()).hexdigest()
            for name in sorted(names)}


def expected_modules(root: Path) -> set[str]:
    return {"JonnyLean"} | {".".join(p.relative_to(root).with_suffix("").parts)
                           for p in (root / "JonnyLean").rglob("*.lean")}


def lake_executable() -> str:
    result = shutil.which("lake")
    fallback = Path.home() / ".elan/bin/lake"
    if result:
        return result
    if fallback.is_file():
        return str(fallback)
    raise OperationError("Lake not found. Install elan and add ~/.elan/bin to PATH.")


def command_step(root: Path, command: list[str], timeout: int, report: dict) -> str:
    start = time.monotonic()
    process = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        output, _ = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
        report["steps"].append({"command": command, "status": "timeout", "output": output})
        raise OperationError(f"Command exceeded {timeout}s: {' '.join(command)}")
    report["steps"].append({"command": command, "exit_code": process.returncode,
                            "seconds": round(time.monotonic() - start, 3), "output": output})
    if process.returncode:
        raise OperationError(f"Command failed ({process.returncode}): {' '.join(command)}")
    return output


def verify(root: Path, config: dict, task: dict, report: dict, shared: dict | None = None) -> None:
    before = capture_inputs(root, task)
    report["inputs"] = before
    lake = lake_executable()
    timeout = config["timeout_seconds"]
    reusable = shared is not None and shared.get("inputs") == before
    if reusable:
        report["lean_version"] = shared["lean_version"]
        report["steps"] = copy.deepcopy(shared["steps"])
    else:
        report["lean_version"] = command_step(root, [lake, "env", "lean", "--version"], timeout, report).strip()
        command_step(root, [lake, "build"], timeout, report)
    command_step(root, [lake, "env", "lean", "-DwarningAsError=true", task["contract"]], timeout, report)
    if reusable:
        audit = copy.deepcopy(shared["audit"])
    else:
        output = command_step(root, [lake, "env", "lean", "tools/Audit.lean"], timeout, report)
        lines = [line[len(MARKER):] for line in output.splitlines() if line.startswith(MARKER)]
        if len(lines) != 1:
            raise OperationError("Audit must emit exactly one machine-readable result")
        audit = json.loads(lines[0])
    modules, declarations = audit.get("modules"), audit.get("declarations")
    if not isinstance(modules, list) or any(not isinstance(m, str) for m in modules):
        raise OperationError("Invalid audit module list")
    if not isinstance(declarations, list) or not declarations:
        raise OperationError("Empty or invalid declaration audit")
    report["audit"] = audit
    expected = expected_modules(root)
    if set(modules) != expected:
        raise Rejected(f"Module coverage mismatch; uninspected={sorted(expected - set(modules))}, "
                       f"unexpected={sorted(set(modules) - expected)}")
    names = set()
    for declaration in declarations:
        if not isinstance(declaration, dict):
            raise OperationError("Invalid declaration row")
        for key in ("name", "module", "kind", "type"):
            if not isinstance(declaration.get(key), str) or not declaration[key]:
                raise OperationError(f"Invalid declaration field: {key}")
        if declaration["name"] in names or declaration["module"] not in expected:
            raise OperationError("Duplicate declaration or unexpected origin")
        names.add(declaration["name"])
        axioms = declaration.get("axioms")
        if not isinstance(axioms, list) or any(not isinstance(a, str) for a in axioms):
            raise OperationError("Invalid axiom dependency list")
        forbidden = set(axioms) - set(config["allowed_axioms"])
        if "sorryAx" in axioms:
            forbidden.add("sorryAx")
        if forbidden:
            report["findings"].append({"declaration": declaration["name"],
                                        "forbidden_axioms": sorted(forbidden)})
    targets = [d for d in declarations if d["name"] == task["declaration"]]
    if len(targets) != 1 or targets[0]["kind"] != "theorem" or targets[0]["module"] != task["module"]:
        raise Rejected("Configured target must be a named theorem in the specified module")
    report["target"] = targets[0]
    if report["findings"]:
        raise Rejected("Forbidden axioms found in compiled declarations")
    # Anonymous examples need not survive as named environment declarations.
    # Check every covered source with warnings-as-errors as well, including on
    # warm builds, so an unfinished anonymous proof cannot escape the audit.
    if not reusable:
        for module in sorted(expected):
            source = module.replace(".", "/") + ".lean"
            command_step(root, [lake, "env", "lean", "-DwarningAsError=true", source], timeout, report)
    if capture_inputs(root, task) != before:
        raise OperationError("Inputs changed during verification; retry with stable files")
    report["mechanical"] = "pass"
    if shared is not None and not reusable:
        shared.update(inputs=before, lean_version=report["lean_version"], audit=copy.deepcopy(audit),
                      steps=copy.deepcopy(report["steps"]))


def check_review(root: Path, task: dict, report: dict) -> None:
    if not (root / task["review"]).is_file():
        report["review"] = {"status": "missing"}
        raise Rejected("Independent AI review has not been recorded")
    record = json.loads(local_file(root, task["review"]).read_text())
    if not isinstance(record, dict) or record.get("schema") != 1 or record.get("task") != task["id"]:
        raise OperationError("Invalid review record")
    reviewer = record.get("reviewer", {})
    if (not isinstance(reviewer, dict) or reviewer.get("kind") != "ai" or
        not isinstance(reviewer.get("name"), str) or not reviewer["name"].strip()):
        raise OperationError("The initial workflow requires an explicitly labeled AI reviewer")
    report["review"] = {"status": "pending", "reviewer": reviewer,
                         "record": task["review"], "authenticated": False}
    if record.get("inputs") != report["inputs"]:
        report["review"]["status"] = "stale"
        raise Rejected("Reviewed inputs changed; a fresh independent review is required")
    checks = record.get("checks", [])
    if not isinstance(checks, list) or any(not isinstance(c, dict) for c in checks):
        raise OperationError("Invalid review checks")
    keys = [c.get("criterion") for c in checks]
    if any(not isinstance(key, str) for key in keys):
        raise OperationError("Review criterion names must be strings")
    if len(keys) != len(CRITERIA) or set(keys) != CRITERIA:
        raise Rejected("Review must cover every rubric criterion exactly once")
    if (record.get("decision") != "approve" or record.get("findings") != [] or
        any(c.get("result") != "pass" or not isinstance(c.get("evidence"), str) or
            not c["evidence"].strip() for c in checks)):
        report["review"]["status"] = "changes_requested"
        raise Rejected("Independent review has unresolved findings or missing evidence")
    report["review"]["status"] = "approved_current"


def save_report(root: Path, task_id: str, report: dict) -> None:
    destination = root / "artifacts" / task_id
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    lines = [f"# {task_id}: {report['status']}", "", f"- 機械検証: {report['mechanical']}",
             f"- AIレビュー: {report['review']['status']}", "- 人間の承認: 未記録", ""]
    if report.get("target"):
        lines.extend(["## 検査した命題", "", "```lean", report["target"]["type"], "```", "",
                      f"公理依存: {json.dumps(report['target']['axioms'])}", ""])
    if report.get("error"):
        lines.extend(["## 停止理由", "", report["error"], ""])
    for finding in report["findings"]:
        lines.append(f"- {finding['declaration']}: {', '.join(finding['forbidden_axioms'])}")
    lines.extend(["", "入力のSHA-256と実行ログは `report.json` を参照。",
                  "レビュー記録は自己申告であり、電子署名や自然言語との同値性証明ではありません。", ""])
    (destination / "report.md").write_text("\n".join(lines))


def run_one(root: Path, task_id: str, command: str, shared: dict | None = None) -> int:
    report = {"schema": 1, "task": task_id, "status": "error", "mechanical": "not_completed",
              "review": {"status": "not_checked"}, "human_approval": "not_recorded",
              "steps": [], "findings": []}
    exit_code = 2
    try:
        config, task = load_task(root, task_id)
        verify(root, config, task, report, shared)
        if command in ("review", "run"):
            check_review(root, task, report)
        report["status"] = "pass"
        exit_code = 0
    except Rejected as error:
        report["status"], report["error"] = "fail", str(error)
        if report["mechanical"] != "pass":
            report["mechanical"] = "fail"
        exit_code = 1
    except (OperationError, OSError, ValueError, TypeError, KeyError) as error:
        report["error"] = str(error)
    try:
        save_report(root, task_id, report)
    except OSError as error:
        report["status"], report["error"] = "error", f"Could not save report: {error}"
        exit_code = 2
    print(f"{task_id}: {report['status'].upper()} | Lean={report['mechanical']} | AI review={report['review']['status']}")
    if "error" in report:
        print(report["error"], file=sys.stderr)
    return exit_code


def main() -> int:
    default_root = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(default_root))
    if __name__ == "__main__":
        sys.modules["tools.jonnylean"] = sys.modules[__name__]
    argv = sys.argv[1:]
    if argv and argv[0] in {"doctor", "status", "work", "resume", "adopt", "report"}:
        from worker.cli import main as worker_main
        return worker_main(default_root, argv)
    if argv and argv[0] == "pr":
        from tools.publish import main as publish_main
        return publish_main(default_root, argv[1:])
    parser = argparse.ArgumentParser(description=__doc__, epilog=
        "Worker: doctor | status | work | resume | adopt | report. GitHub: pr. HTML: dashboard.")
    parser.add_argument("command", choices=("verify", "review", "run", "fingerprint", "dashboard"))
    parser.add_argument("task", nargs="?", default="all")
    parser.add_argument("--project", type=Path, default=default_root)
    args = parser.parse_args()
    if args.task != "all" and not re.fullmatch(r"JL-\d{3}", args.task):
        parser.error("Task must be all or have the form JL-001")
    root = args.project.resolve()
    lock = root / ".jonnylean.lock"
    acquired = False
    try:
        data = tomllib.loads(local_file(root, "jonnylean.toml").read_text())
        if not isinstance(data.get("tasks"), list) or any(not isinstance(t, dict) for t in data["tasks"]):
            raise OperationError("tasks must be an array of tables")
        ids = [t["id"] for t in data["tasks"]] if args.task == "all" else [args.task]
        if not ids:
            raise OperationError("No tasks configured")
        for task_id in ids:
            if not isinstance(task_id, str) or not re.fullmatch(r"JL-\d{3}", task_id):
                raise OperationError("Invalid task ID")
            load_task(root, task_id)
        if args.command == "fingerprint":
            values = [{"task": task_id, "inputs": capture_inputs(root, load_task(root, task_id)[1])}
                      for task_id in ids]
            print(json.dumps(values if args.task == "all" else values[0], ensure_ascii=False, indent=2))
            return 0
        try:
            with lock.open("x") as stream:
                stream.write(str(os.getpid()))
            acquired = True
        except FileExistsError:
            raise OperationError("Another run holds .jonnylean.lock; wait for it to finish")
        exit_code = 0
        if args.command != "dashboard":
            shared: dict = {}
            for task_id in ids:
                exit_code = max(exit_code, run_one(root, task_id, args.command, shared))
        from tools.reporting import render_dashboard
        path = render_dashboard(root)
        print(f"Report: {path}")
        return exit_code
    except (OperationError, OSError, ValueError, TypeError, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 2
    finally:
        if acquired:
            lock.unlink(missing_ok=True)


if __name__ == "__main__":
    sys.exit(main())

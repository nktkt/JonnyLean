"""Registry, dependency graph, theorem search, and deterministic catalog builds."""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

from tools.scopes import module_graph, task_scope

FIELDS = ("id", "title", "domain", "description", "tags", "spec", "module", "declaration",
          "contract", "review", "editable", "depends_on")


def registry(root: Path) -> list[dict]:
    config = tomllib.loads((root / "jonnylean.toml").read_text())
    tasks = config.get("tasks")
    if not isinstance(tasks, list) or not tasks:
        raise ValueError("Task registry must be a nonempty array")
    from tools.jonnylean import load_task
    for task in tasks:
        load_task(root, task["id"])
    return tasks


def select(tasks: list[dict], *, domain=None, tag=None, query=None) -> list[dict]:
    return [t for t in tasks
            if (not domain or t.get("domain", "").casefold() == domain.casefold())
            and (not tag or tag in t.get("tags", []))
            and (not query or query.casefold() in json.dumps(t, ensure_ascii=False).casefold())]


def affected(root: Path, tasks: list[dict], paths: list[str]) -> list[dict]:
    if any(not p.startswith(("JonnyLean/", "specs/", "contracts/")) for p in paths):
        return tasks
    from tools.jonnylean import capture_inputs
    return [task for task in tasks if set(paths) & set(capture_inputs(root, task))]


def changed_paths(root: Path, ref: str) -> list[str]:
    def git(*args):
        result = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, timeout=30)
        if result.returncode:
            raise ValueError(result.stderr.strip() or "Cannot inspect Git changes")
        return result.stdout
    # Resolve first so user input is never treated as an option or a pathspec.
    commit = git("rev-parse", "--verify", "--end-of-options", ref + "^{commit}").strip()
    changed = git("diff", "--name-only", "-z", commit, "--").split("\0")
    changed += git("ls-files", "--others", "--exclude-standard", "-z").split("\0")
    return sorted(set(p for p in changed if p and not p.startswith(("artifacts/", ".jonnylean/"))))


def task_edges(tasks: list[dict]) -> list[dict]:
    return [{"from": dependency, "to": task["id"]} for task in tasks for dependency in task.get("depends_on", [])]


def generated(root: Path) -> tuple[str, str, list[dict]]:
    root = root.resolve()
    tasks = []
    for path in sorted((root / "catalog/fragments").glob("*.json")):
        fragment = json.loads(path.read_text())
        if not isinstance(fragment, list) or any(not isinstance(t, dict) for t in fragment):
            raise ValueError(f"Invalid catalog fragment: {path}")
        tasks.extend(fragment)
    if not tasks:
        raise ValueError("No catalog fragments")
    seen_ids, seen_declarations = set(), set()
    graph = module_graph(root)
    for task in tasks:
        if set(task) != set(FIELDS):
            raise ValueError(f"Catalog fields differ for {task.get('id')}: {set(task) ^ set(FIELDS)}")
        if not re.fullmatch(r"JL-\d{3}", task["id"]) or task["id"] in seen_ids:
            raise ValueError("Invalid or duplicate catalog ID")
        if not isinstance(task["declaration"], str) or not task["declaration"] or task["declaration"] in seen_declarations:
            raise ValueError("Invalid or duplicate catalog declaration")
        seen_ids.add(task["id"]); seen_declarations.add(task["declaration"])
        if task["module"] not in graph:
            raise ValueError(f"Missing module for {task['id']}")
        for key in ("title", "domain", "description"):
            if not isinstance(task[key], str) or not task[key]:
                raise ValueError(f"Empty {key} for {task['id']}")
        for key in ("tags", "editable", "depends_on"):
            if not isinstance(task[key], list) or any(not isinstance(x, str) for x in task[key]):
                raise ValueError(f"Invalid {key} for {task['id']}")
        for key in ("spec", "contract"):
            path = root / task[key]
            if not path.resolve().is_relative_to(root) or not path.is_file():
                raise ValueError(f"Missing catalog {key}: {task[key]}")
        for name in task['editable']:
            path = root / name
            if (not name.startswith('JonnyLean/') or not name.endswith('.lean') or '..' in Path(name).parts
                or path.is_symlink() or not path.resolve().is_relative_to(root) or not path.is_file()):
                raise ValueError(f"Editable catalog paths must be existing mathematics Lean files: {name}")
        if task["review"] != f"reviews/{task['id']}.json":
            raise ValueError(f"Unexpected review path for {task['id']}")
    tasks.sort(key=lambda t: t["id"])
    for task in tasks:
        scope = task_scope(root, task, graph)
        inferred = [other["id"] for other in tasks if other["module"] in scope
                    and other["module"] != task["module"]]
        task["depends_on"] = sorted(set(task["depends_on"] + inferred))
        if any(dep not in seen_ids or dep == task["id"] for dep in task["depends_on"]):
            raise ValueError(f"Invalid dependencies for {task['id']}")
    # Topological elimination avoids repeatedly traversing every path in a diamond.
    remaining = {t["id"]: set(t["depends_on"]) for t in tasks}
    while remaining:
        ready = {name for name, deps in remaining.items() if not deps}
        if not ready:
            raise ValueError("Catalog dependencies contain a cycle")
        remaining = {name: deps - ready for name, deps in remaining.items() if name not in ready}
    config = tomllib.loads((root / "jonnylean.toml").read_text())
    lines = ["# Generated by `python3 tools/jonnylean.py catalog sync`; edit catalog/fragments/.",
             "schema = 1", f"timeout_seconds = {config['timeout_seconds']}",
             "allowed_axioms = " + json.dumps(config["allowed_axioms"]), ""]
    for task in tasks:
        lines.append("[[tasks]]")
        lines.extend(f"{key} = {json.dumps(task[key], ensure_ascii=False)}" for key in FIELDS)
        lines.append("")
    imports = "".join(f"import {name}\n" for name in sorted(graph) if name != "JonnyLean")
    return "\n".join(lines), imports, tasks


def statistics(root: Path, tasks: list[dict]) -> dict:
    result = {"tasks": len(tasks), "domains": dict(sorted(Counter(t.get("domain", "unclassified") for t in tasks).items())),
              "math_modules": len(list((root / "JonnyLean").rglob("*.lean"))),
              "dependency_edges": len(task_edges(tasks))}
    from tools.jonnylean import capture_verification_inputs
    current = capture_verification_inputs(root)
    for path in sorted((root / "artifacts").glob("JL-*/report.json")):
        try:
            report = json.loads(path.read_text())
            if report.get("mechanical") != "pass" or report.get("verification_inputs") != current:
                continue
            declarations = report["audit"]["declarations"]
            result.update(declarations=len(declarations),
                          checked_theorems=sum(d["kind"] == "theorem" for d in declarations),
                          definitions=sum(d["kind"] == "definition" for d in declarations))
            break
        except (OSError, ValueError, KeyError, TypeError, AttributeError):
            continue
    return result


def main(default_root: Path, argv: list[str]) -> int:
    from tools.jonnylean import OperationError
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("list", "show", "stats", "graph", "check", "sync", "search"))
    parser.add_argument("query", nargs="?")
    parser.add_argument("--project", type=Path, default=default_root)
    parser.add_argument("--domain")
    parser.add_argument("--tag")
    parser.add_argument("--format", choices=("json", "mermaid", "text"), default="text")
    args = parser.parse_args(argv)
    root = args.project.resolve()
    try:
        if args.action in ("sync", "check"):
            manifest, imports, tasks = generated(root)
            if args.action == "sync":
                (root / "jonnylean.toml").write_text(manifest)
                (root / "JonnyLean.lean").write_text(imports)
            elif ((root / "jonnylean.toml").read_text() != manifest or
                  (root / "JonnyLean.lean").read_text() != imports):
                raise ValueError("Catalog/root imports out of date; run catalog sync")
            print(f"Catalog {args.action}: {len(tasks)} tasks, {len(imports.splitlines())} mathematics modules")
            return 0
        tasks = registry(root)
        chosen = select(tasks, domain=args.domain, tag=args.tag, query=args.query if args.action in ("list", "search") else None)
        if args.action == "show":
            chosen = [t for t in chosen if t["id"] == args.query]
            if not chosen:
                raise ValueError("Unknown task")
        if args.action == "stats":
            print(json.dumps(statistics(root, chosen), ensure_ascii=False, indent=2)); return 0
        if args.action == "graph":
            ids = {t["id"] for t in chosen}
            edges = [e for e in task_edges(tasks) if e["to"] in ids and e["from"] in ids]
            if args.format == "mermaid":
                print("flowchart LR")
                for task in chosen:
                    print(f'  {task["id"].replace("-", "_")}["{task["id"]}"]')
                for edge in edges:
                    print(f'  {edge["from"].replace("-", "_")} --> {edge["to"].replace("-", "_")}')
            else:
                print(json.dumps({"tasks": chosen, "edges": edges}, ensure_ascii=False, indent=2))
            return 0
        if args.format == "json" or args.action == "show":
            print(json.dumps(chosen, ensure_ascii=False, indent=2))
        else:
            for task in chosen:
                print(f'{task["id"]:7} {task.get("domain", "unclassified"):20} {task["title"]}  {task["declaration"]}')
        return 0
    except (OperationError, OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr); return 2

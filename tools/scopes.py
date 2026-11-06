"""Source dependency scopes, cross-checked against Lean's compiled import graph.

The header reader intentionally supports this repository's ASCII module paths.
Unsupported headers fail closed; it is not a general-purpose Lean parser.
"""
from __future__ import annotations

import re
from pathlib import Path


def imports(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    pos, names = 0, []
    def whitespace(index: int) -> int:
        while index < len(text):
            if text[index].isspace() or text[index] == "\ufeff":
                index += 1
            elif text.startswith("--", index):
                end = text.find("\n", index)
                index = len(text) if end < 0 else end + 1
            elif text.startswith("/-", index):
                depth, index = 1, index + 2
                while depth and index < len(text):
                    if text.startswith("/-", index):
                        depth, index = depth + 1, index + 2
                    elif text.startswith("-/", index):
                        depth, index = depth - 1, index + 2
                    else:
                        index += 1
                if depth:
                    raise ValueError(f"Unclosed Lean comment: {path}")
            else:
                break
        return index
    def word(index: int):
        index = whitespace(index)
        match = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", text[index:])
        return (match.group(), index + len(match.group())) if match else (None, index)
    for _ in range(10000):
        token, end = word(pos)
        if token in ("module", "prelude"):
            pos = end
            continue
        if token in ("public", "meta"):
            token, end = word(end)
            if token == "meta":
                token, end = word(end)
        if token != "import":
            return names
        name, end = word(end)
        if name == "all":
            name, end = word(end)
        if not name or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", name):
            raise ValueError(f"Unsupported module import in {path}")
        names.append(name)
        pos = end
    raise ValueError(f"Unreasonably long Lean header: {path}")


def module_graph(root: Path) -> dict[str, list[str]]:
    paths = [root / "JonnyLean.lean", *(root / "JonnyLean").rglob("*.lean")]
    return {".".join(p.relative_to(root).with_suffix("").parts):
            sorted(n for n in imports(p) if n == "JonnyLean" or n.startswith("JonnyLean."))
            for p in paths}


def closure(graph: dict[str, list[str]], roots: list[str]) -> set[str]:
    found, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module in found:
            continue
        if module not in graph:
            raise ValueError(f"Missing project module: {module}")
        found.add(module)
        pending.extend(graph[module])
    return found


def task_scope(root: Path, task: dict, graph=None) -> set[str]:
    graph = module_graph(root) if graph is None else graph
    contract_imports = [n for n in imports(root / task["contract"])
                        if n == "JonnyLean" or n.startswith("JonnyLean.")]
    return closure(graph, [task["module"], *contract_imports])


def check_compiled_graph(root: Path, audit: dict) -> None:
    records = audit.get("imports")
    if not isinstance(records, list):
        raise ValueError("Compiled module import graph is missing")
    graph = module_graph(root)
    actual = {}
    for record in records:
        if (not isinstance(record, dict) or not isinstance(record.get("module"), str)
            or not isinstance(record.get("imports"), list)
            or any(not isinstance(n, str) for n in record["imports"])):
            raise ValueError("Invalid compiled import graph")
        if record["module"] in actual:
            raise ValueError("Duplicate compiled import graph entry")
        actual[record["module"]] = sorted(n for n in record["imports"]
                                           if n == "JonnyLean" or n.startswith("JonnyLean."))
    if actual != graph:
        raise ValueError("Source import scopes disagree with Lean's compiled module imports")

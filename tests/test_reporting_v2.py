"""Fast dashboard checks using synthetic fingerprints and review fixtures only."""
from __future__ import annotations

import base64
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tools.jonnylean import CRITERIA, capture_inputs, capture_verification_inputs
from tools.reporting import render_dashboard


class DashboardParser(HTMLParser):
    def __init__(self, source):
        super().__init__()
        self.cards = {}
        self.controls = {}
        self.scripts = []
        self.csp = ""
        self.current = None
        self.in_script = False
        self.feed(source)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "article":
            self.current = {"attrs": attrs, "text": "", "links": []}
            self.cards[attrs["id"]] = self.current
        if tag == "a" and self.current is not None:
            self.current["links"].append(attrs["href"])
        if tag in {"input", "select", "button"}:
            self.controls[attrs.get("id")] = attrs
        if tag == "script":
            self.in_script = True
            self.scripts.append("")
        if tag == "meta" and attrs.get("http-equiv") == "Content-Security-Policy":
            self.csp = attrs["content"]

    def handle_endtag(self, tag):
        if tag == "article":
            self.current = None
        if tag == "script":
            self.in_script = False

    def handle_data(self, data):
        if self.current is not None:
            self.current["text"] += data
        if self.in_script:
            self.scripts[-1] += data


class DashboardV2Tests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="jonnylean-dashboard-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        for directory in ("JonnyLean", "contracts", "specs", "reviews", "tools"):
            (self.root / directory).mkdir()
        for name, text in {
            "lean-toolchain": "leanprover/lean4:v4.29.1\n",
            "lakefile.toml": 'name = "fixture"\n',
            "lake-manifest.json": "{}\n",
            "tools/Audit.lean": "import Lean\n",
            "reviews/rubric.md": "Synthetic fixture: not a real review.\n",
        }.items():
            (self.root / name).write_text(text)
        self.make_tasks(3)

    def make_tasks(self, count):
        self.tasks = []
        imports = []
        for number in range(1, count + 1):
            task = {
                "id": f"JL-{number:03}", "title": f"Fixture {number}",
                "domain": "logic" if number % 2 else "algorithms",
                "description": "Synthetic dashboard fixture", "tags": ["fixture"],
                "module": f"JonnyLean.Fixture{number}",
                "declaration": f"JonnyLean.fixture{number}",
                "spec": f"specs/JL-{number:03}.md", "contract": f"contracts/JL{number:03}.lean",
                "review": f"reviews/JL-{number:03}.json", "editable": [f"JonnyLean/Fixture{number}.lean"],
                "depends_on": ["JL-001"] if number == 2 else [],
            }
            self.tasks.append(task)
            header = "import JonnyLean.Fixture1\n" if number == 2 else ""
            (self.root / task["editable"][0]).write_text(header + f"theorem fixture{number} : True := True.intro\n")
            (self.root / task["contract"]).write_text(f"import {task['module']}\n")
            (self.root / task["spec"]).write_text(task["description"])
            imports.append(f"import {task['module']}\n")
        (self.root / "JonnyLean.lean").write_text("".join(imports))
        self.write_config()

    def write_config(self):
        lines = ["schema = 1", "timeout_seconds = 120", 'allowed_axioms = ["propext", "Quot.sound"]']
        for task in self.tasks:
            lines.append("[[tasks]]")
            lines.extend(f"{key} = {json.dumps(value, ensure_ascii=False)}" for key, value in task.items())
        (self.root / "jonnylean.toml").write_text("\n".join(lines) + "\n")

    def review(self, index=0):
        task = self.tasks[index]
        record = {
            "schema": 1, "task": task["id"],
            "reviewer": {"kind": "ai", "name": "Synthetic fixture; not independent approval"},
            "decision": "approve", "findings": [], "inputs": capture_inputs(self.root, task),
            "checks": [{"criterion": criterion, "result": "pass", "evidence": "Synthetic fixture only"}
                       for criterion in sorted(CRITERIA)],
        }
        (self.root / task["review"]).write_text(json.dumps(record))
        return record

    def report(self, index=0, approved=False):
        task = self.tasks[index]
        report = {
            "status": "pass", "mechanical": "pass", "inputs": capture_inputs(self.root, task),
            "verification_inputs": capture_verification_inputs(self.root),
            "target": {"type": "∀ n : Nat, n = n", "axioms": []},
            "review": {"status": "approved_current" if approved else "not_checked"},
        }
        path = self.root / "artifacts" / task["id"] / "report.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(report))
        return path, report

    def dashboard(self):
        source = render_dashboard(self.root).read_text()
        return source, DashboardParser(source)

    def test_global_change_stales_verification_without_staling_unrelated_review(self):
        self.review()
        _, report = self.report(approved=True)
        _, current = self.dashboard()
        self.assertEqual(current.cards["JL-001"]["attrs"]["data-status"], "pass")
        unrelated = self.root / self.tasks[2]["editable"][0]
        unrelated.write_text(unrelated.read_text() + "-- unrelated change\n")
        self.assertEqual(report["inputs"], capture_inputs(self.root, self.tasks[0]))
        self.assertNotEqual(report["verification_inputs"], capture_verification_inputs(self.root))
        _, parsed = self.dashboard()
        card = parsed.cards["JL-001"]
        self.assertEqual(card["attrs"]["data-status"], "stale")
        self.assertIn("全体検証の再実行が必要", card["text"])
        self.assertIn("approved_current", card["text"])
        dependent = self.root / self.tasks[0]["spec"]
        dependent.write_text("Changed reviewed specification\n")
        _, parsed = self.dashboard()
        self.assertNotIn("approved_current", parsed.cards["JL-001"]["text"])

    def test_legacy_report_without_global_fingerprint_is_stale(self):
        path, report = self.report()
        del report["verification_inputs"]
        path.write_text(json.dumps(report))
        _, parsed = self.dashboard()
        self.assertEqual(parsed.cards["JL-001"]["attrs"]["data-status"], "stale")

    def test_current_approval_is_rechecked_after_invalid_revoked_or_deleted_record(self):
        record = self.review()
        self.report(approved=True)
        review_path = self.root / self.tasks[0]["review"]
        mutations = (
            ({**record, "checks": [{"criterion": []}]}, "invalid"),
            ({**record, "decision": "changes_requested", "findings": ["Synthetic revocation"]}, "changes_requested"),
            (None, "missing"),
        )
        for changed, status in mutations:
            with self.subTest(status=status):
                if changed is None:
                    review_path.unlink()
                else:
                    review_path.write_text(json.dumps(changed))
                _, parsed = self.dashboard()
                card = parsed.cards["JL-001"]
                self.assertEqual(card["attrs"]["data-status"], "fail")
                self.assertIn(status, card["text"])
                self.assertNotIn("approved_current", card["text"])

    def test_malformed_reports_do_not_break_catalog(self):
        path, _ = self.report()
        for malformed in ("{", "[]", '{"target": []}', '{"review": []}',
                          '{"target": {"axioms": {}}}', '{"verification_inputs": []}'):
            with self.subTest(malformed=malformed):
                path.write_text(malformed)
                _, parsed = self.dashboard()
                self.assertEqual(len(parsed.cards), 3)
                self.assertEqual(parsed.cards["JL-001"]["attrs"]["data-status"], "not_run")

    def test_sixty_tasks_have_search_controls_dependencies_and_local_links(self):
        self.make_tasks(60)
        _, parsed = self.dashboard()
        self.assertEqual(len(parsed.cards), 60)
        self.assertTrue({"query", "domain", "status", "reset-filters"} <= set(parsed.controls))
        links = parsed.cards["JL-002"]["links"]
        self.assertIn("#JL-001", links)
        for path in ("../specs/JL-002.md", "../JonnyLean/Fixture2.lean", "../contracts/JL002.lean",
                     "../reviews/JL-002.json", "../artifacts/JL-002/report.json"):
            self.assertIn(path, links)
        for card in parsed.cards.values():
            self.assertIn(card["attrs"]["id"], card["attrs"]["data-search"])
            self.assertIn(card["attrs"]["data-domain"], {"logic", "algorithms"})

    def test_text_is_escaped_and_script_is_static_with_no_network_permissions(self):
        attack = '<script>alert("fixture")</script> & " onfocus="bad()'
        self.tasks[0]["title"] = attack
        self.tasks[0]["domain"] = attack
        self.tasks[0]["description"] = attack
        self.write_config()
        path, report = self.report()
        report["target"]["type"] = attack
        report["error"] = attack
        path.write_text(json.dumps(report))
        source, parsed = self.dashboard()
        self.assertNotIn("<script>", source)
        self.assertNotIn(attack, source)
        self.assertIn("&lt;script&gt;", source)
        self.assertEqual(parsed.cards["JL-001"]["attrs"]["data-domain"], attack)
        self.assertEqual(len(parsed.scripts), 1)
        self.assertNotIn("fixture", parsed.scripts[0])
        script_hash = base64.b64encode(hashlib.sha256(parsed.scripts[0].encode()).digest()).decode()
        self.assertIn(f"script-src 'sha256-{script_hash}'", parsed.csp)
        self.assertIn("connect-src 'none'", parsed.csp)
        self.assertIn("default-src 'none'", parsed.csp)
        self.assertNotIn("innerHTML", parsed.scripts[0])

    @unittest.skipUnless(shutil.which("node"), "Node is optional; only used to exercise the static UI script")
    def test_browser_filter_combines_query_domain_status_and_resets(self):
        _, parsed = self.dashboard()
        harness = r'''
const assert = require('node:assert/strict');
const cards = [
  {dataset: {search: 'JL-001 Alpha theorem', domain: 'logic', status: 'pass'}},
  {dataset: {search: 'JL-002 Beta theorem', domain: 'algorithms', status: 'pass'}},
  {dataset: {search: 'JL-003 Alpha lemma', domain: 'logic', status: 'stale'}}
];
const controls = {};
for (const id of ['query', 'domain', 'status', 'visible-count', 'empty-results', 'reset-filters']) {
  controls[id] = {value: '', events: {}, addEventListener(name, callback) { this.events[name] = callback; },
    focus() { this.focused = true; }};
}
global.document = {querySelectorAll() { return cards; }, getElementById(id) { return controls[id]; }};
'''
        checks = r'''
assert.equal(cards.filter(card => !card.hidden).length, 3);
controls.query.value = 'ALPHA theorem'; controls.query.events.input();
assert.deepEqual(cards.map(card => card.hidden), [false, true, true]);
controls.query.value = ''; controls.domain.value = 'logic'; controls.domain.events.change();
controls.status.value = 'stale'; controls.status.events.change();
assert.deepEqual(cards.map(card => card.hidden), [true, true, false]);
assert.equal(controls['visible-count'].textContent, '1 / 3 件を表示');
controls.query.value = 'missing'; controls.query.events.input();
assert.equal(controls['empty-results'].hidden, false);
controls['reset-filters'].events.click();
assert.deepEqual(cards.map(card => card.hidden), [false, false, false]);
assert.equal(controls['empty-results'].hidden, true);
assert.equal(controls.query.focused, true);
'''
        result = subprocess.run([shutil.which("node"), "-"], input=harness + parsed.scripts[0] + checks,
                                text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()

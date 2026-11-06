"""Integration checks against real Lean, using disposable project copies.

The review fixtures below are deliberately synthetic. They test the review gate;
they are not independent reviews and never write approval records to the project.
Run with: python3 -m unittest discover -s tests -v
"""
from __future__ import annotations

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest


PROJECT = Path(__file__).resolve().parents[1]
TASK = "JL-001"
PARITY = Path("JonnyLean/NumberTheory/Parity.lean")
FIXTURE_EVIDENCE = {
    "definition": "Synthetic fixture only: tests recording a definition check, not a real review.",
    "quantifiers": "Synthetic fixture only: tests recording a quantifier check, not a real review.",
    "assumptions": "Synthetic fixture only: tests recording an assumption check, not a real review.",
    "conclusion": "Synthetic fixture only: tests recording a conclusion check, not a real review.",
    "proof": "Synthetic fixture only: tests recording a proof check, not a real review.",
    "coverage": "Synthetic fixture only: tests recording module and declaration coverage.",
    "audit": "Synthetic fixture only: tests binding a record to the fingerprint command output.",
}


class PipelineIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        # Freeze only source inputs, never reuse the real project's compiled
        # objects, generated reports, lock, or approval record.
        cls.sandbox = tempfile.TemporaryDirectory(prefix="jonnylean-integration-")
        cls.addClassCleanup(cls.sandbox.cleanup)
        cls.seed = Path(cls.sandbox.name) / "source"
        shutil.copytree(
            PROJECT,
            cls.seed,
            ignore=shutil.ignore_patterns(
                ".lake", ".git", ".jonnylean", "artifacts", "__pycache__", ".jonnylean.lock"
            ),
        )
        config = tomllib.loads((cls.seed / "jonnylean.toml").read_text())
        cls.tasks = config["tasks"]
        cls.task = next(task for task in config["tasks"] if task["id"] == TASK)
        for task in cls.tasks:
            (cls.seed / task["review"]).unlink(missing_ok=True)
        cls.modules = {"JonnyLean"} | {
            ".".join(path.relative_to(cls.seed).with_suffix("").parts)
            for path in (cls.seed / "JonnyLean").rglob("*.lean")
        }

    def setUp(self) -> None:
        self.project = Path(self.sandbox.name) / self._testMethodName
        shutil.copytree(self.seed, self.project)
        self.report_path = self.project / "artifacts" / TASK / "report.json"

    def cli(self, command: str, expected: int, task_id: str = TASK) -> subprocess.CompletedProcess[str]:
        result = subprocess.run(
            [
                sys.executable,
                str(self.project / "tools/jonnylean.py"),
                command,
                task_id,
                "--project",
                str(self.project),
            ],
            cwd=self.project,
            text=True,
            capture_output=True,
            timeout=240,
            check=False,
        )
        self.assertEqual(
            result.returncode,
            expected,
            f"{command}: expected exit {expected}, got {result.returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}",
        )
        return result

    def report(self) -> dict:
        return json.loads(self.report_path.read_text())

    def append_math(self, source: str) -> None:
        path = self.project / PARITY
        path.write_text(path.read_text() + "\n" + source + "\n")

    def replace_math(self, original: str, replacement: str) -> None:
        path = self.project / PARITY
        source = path.read_text()
        self.assertEqual(source.count(original), 1, "Expected one fixture mutation point")
        path.write_text(source.replace(original, replacement))

    def synthetic_review(self, task_id: str = TASK) -> dict:
        fingerprint = json.loads(self.cli("fingerprint", 0, task_id).stdout)
        record = {
            "schema": 1,
            "task": task_id,
            "reviewer": {
                "kind": "ai",
                "name": "synthetic test fixture (not a real review)",
            },
            "decision": "approve",
            "findings": [],
            "inputs": fingerprint["inputs"],
            "checks": [
                {"criterion": criterion, "result": "pass", "evidence": evidence}
                for criterion, evidence in FIXTURE_EVIDENCE.items()
            ],
        }
        self.write_review(record, task_id)
        return record

    def write_review(self, record: object, task_id: str = TASK) -> None:
        task = next(task for task in self.tasks if task["id"] == task_id)
        destination = self.project / task["review"]
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")

    def assert_forbidden(self, declaration: str, axiom: str) -> None:
        report = self.report()
        matching = [row for row in report["findings"] if row["declaration"] == declaration]
        self.assertEqual(len(matching), 1, report)
        self.assertIn(axiom, matching[0]["forbidden_axioms"])
        self.assertEqual(report["status"], "fail")

    def assert_contract_failure(self) -> None:
        self.cli("verify", 2)
        report = self.report()
        self.assertEqual(report["status"], "error")
        self.assertEqual(report["steps"][-1]["command"][-1], self.task["contract"])
        self.assertNotEqual(report["steps"][-1]["exit_code"], 0)

    def test_valid_theorem_passes_real_lean_and_audit(self) -> None:
        self.cli("verify", 0)
        report = self.report()
        self.assertEqual(report["mechanical"], "pass")
        self.assertEqual(report["target"]["name"], "JonnyLean.even_add")
        self.assertEqual(report["target"]["kind"], "theorem")
        self.assertEqual(report["target"]["axioms"], [])
        self.assertEqual(report["findings"], [])
        self.assertEqual(report["review"]["status"], "not_checked")
        self.assertEqual(set(report["audit"]["modules"]), self.modules)
        config = tomllib.loads((self.project / "jonnylean.toml").read_text())
        self.assertEqual(set(config["allowed_axioms"]), {"propext", "Quot.sound"})
        self.assertNotIn("sorryAx", config["allowed_axioms"])

    def test_unused_sorry_outside_project_namespace_is_rejected(self) -> None:
        self.append_math("def CompletelyUnrelated.unused : Nat := by sorry")
        self.cli("verify", 1)
        self.assert_forbidden("CompletelyUnrelated.unused", "sorryAx")

    def test_anonymous_sorry_is_rejected_by_strict_source_compilation(self) -> None:
        # Anonymous examples need not persist as imported declarations, so the
        # strict Lean source pass must catch their unfinished proofs as well.
        self.append_math("example : False := by sorry")
        self.cli("verify", 2)
        report = self.report()
        self.assertEqual(report["status"], "error")
        self.assertEqual(report["findings"], [])
        failed_step = report["steps"][-1]
        self.assertEqual(failed_step["command"][-1], str(PARITY))
        self.assertIn("-DwarningAsError=true", failed_step["command"])
        self.assertNotEqual(failed_step["exit_code"], 0)
        self.assertIn("sorry", failed_step["output"])

    def test_transitive_sorry_through_private_helper_is_rejected(self) -> None:
        self.append_math(
            "namespace AuditProbe\n"
            "private def hidden : Nat := by sorry\n"
            "def throughHelper : Nat := hidden\n"
            "end AuditProbe"
        )
        self.cli("verify", 1)
        self.assert_forbidden("AuditProbe.throughHelper", "sorryAx")
        hidden = [
            row for row in self.report()["audit"]["declarations"]
            if row["name"].startswith("_private.") and row["name"].endswith("AuditProbe.hidden")
        ]
        self.assertEqual(len(hidden), 1)
        self.assertIn("sorryAx", hidden[0]["axioms"])

    def test_unused_custom_axiom_is_rejected(self) -> None:
        self.append_math("axiom AuditProbe.unused : False")
        self.cli("verify", 1)
        self.assert_forbidden("AuditProbe.unused", "AuditProbe.unused")

    def test_custom_axiom_dependency_in_derived_theorem_is_rejected(self) -> None:
        self.append_math(
            "axiom AuditProbe.assumed : False\n"
            "theorem AuditProbe.derived : 0 = 1 := False.elim AuditProbe.assumed"
        )
        self.cli("verify", 1)
        self.assert_forbidden("AuditProbe.derived", "AuditProbe.assumed")

    def test_extra_false_assumption_fails_independent_contract(self) -> None:
        self.replace_math("(hb : Even b) :", "(hb : Even b) (_extra : False) :")
        self.assert_contract_failure()

    def test_vacuous_even_definition_fails_independent_contract(self) -> None:
        (self.project / PARITY).write_text(
            "import Init\n"
            "namespace JonnyLean\n"
            "def Even (_n : Nat) : Prop := True\n"
            "theorem even_add (a b : Nat) (_ha : Even a) (_hb : Even b) :\n"
            "    Even (a + b) := True.intro\n"
            "end JonnyLean\n"
        )
        # Preserve the dependent task's well-typedness so this mutation tests
        # the independent contract, rather than stopping at its Lean build.
        consecutive = self.project / "JonnyLean/NumberTheory/Consecutive.lean"
        source = consecutive.read_text()
        start = source.index("theorem even_consecutive_product")
        consecutive.write_text(
            source[:start] +
            "theorem even_consecutive_product (n : Nat) : Even (n * (n + 1)) :=\n"
            "  True.intro\n\nend JonnyLean\n"
        )
        self.assert_contract_failure()

    def test_unimported_mathematics_module_is_rejected(self) -> None:
        (self.project / "JonnyLean/Unimported.lean").write_text(
            "theorem Uninspected.truth : True := True.intro\n"
        )
        self.cli("verify", 1)
        report = self.report()
        self.assertIn("Module coverage mismatch", report["error"])
        self.assertIn("JonnyLean.Unimported", report["error"])

    def test_imported_empty_module_counts_toward_coverage(self) -> None:
        (self.project / "JonnyLean/Empty.lean").write_text("-- No declarations.\n")
        root_import = self.project / "JonnyLean.lean"
        root_import.write_text(root_import.read_text() + "\nimport JonnyLean.Empty\n")
        self.cli("verify", 0)
        self.assertIn("JonnyLean.Empty", self.report()["audit"]["modules"])

    def test_missing_configured_target_is_rejected_after_compilation(self) -> None:
        config = self.project / "jonnylean.toml"
        source = config.read_text()
        source = source.replace(
            'declaration = "JonnyLean.even_add"',
            'declaration = "JonnyLean.nonexistent"',
        )
        config.write_text(source)
        self.cli("verify", 1)
        report = self.report()
        self.assertIn("Configured target", report["error"])
        self.assertTrue(all(step.get("exit_code") == 0 for step in report["steps"]))

    def test_broken_proof_fails_lean_build(self) -> None:
        self.replace_math("refine ⟨ka + kb, ?_⟩", "exact False.elim True.intro")
        self.cli("verify", 2)
        report = self.report()
        self.assertEqual(report["status"], "error")
        self.assertEqual(report["steps"][-1]["command"][-1], "build")
        self.assertNotEqual(report["steps"][-1]["exit_code"], 0)

    def test_sorry_in_contract_is_rejected(self) -> None:
        contract = self.project / self.task["contract"]
        contract.write_text(contract.read_text() + "\nexample : False := by sorry\n")
        self.assert_contract_failure()

    def test_review_lifecycle_missing_current_then_stale_spec(self) -> None:
        self.cli("run", 1)
        self.assertEqual(self.report()["mechanical"], "pass")
        self.assertEqual(self.report()["review"]["status"], "missing")

        self.synthetic_review()
        self.cli("run", 0)
        report = self.report()
        self.assertEqual(report["review"]["status"], "approved_current")
        self.assertFalse(report["review"]["authenticated"])
        self.assertEqual(report["human_approval"], "not_recorded")

        spec = self.project / self.task["spec"]
        spec.write_text(spec.read_text() + "\nSynthetic test fixture: the specification changed.\n")
        self.cli("run", 1)
        self.assertEqual(self.report()["mechanical"], "pass")
        self.assertEqual(self.report()["review"]["status"], "stale")

    def test_definition_edit_invalidates_review_even_when_lean_still_passes(self) -> None:
        self.synthetic_review()
        self.replace_math("∃ k : Nat, n = 2 * k", "∃ witness : Nat, n = 2 * witness")
        self.cli("run", 1)
        self.assertEqual(self.report()["mechanical"], "pass")
        self.assertEqual(self.report()["review"]["status"], "stale")

    def test_malformed_review_record_is_rejected(self) -> None:
        self.write_review(["Synthetic malformed review fixture"])
        self.cli("run", 2)
        report = self.report()
        self.assertEqual(report["mechanical"], "pass")
        self.assertEqual(report["status"], "error")
        self.assertIn("Invalid review record", report["error"])

    def test_review_without_all_criteria_is_rejected(self) -> None:
        record = self.synthetic_review()
        record["checks"].pop()
        self.write_review(record)
        self.cli("run", 1)
        self.assertEqual(self.report()["mechanical"], "pass")
        self.assertIn("every rubric criterion", self.report()["error"])

    def test_duplicate_configured_declarations_are_rejected(self) -> None:
        config = self.project / "jonnylean.toml"
        config.write_text(config.read_text().replace(
            'declaration = "JonnyLean.even_consecutive_product"',
            'declaration = "JonnyLean.even_add"',
        ))
        result = self.cli("verify", 2)
        self.assertIn("unique", result.stderr)
        self.assertFalse((self.project / ".jonnylean.lock").exists())

    def test_cyclic_dependencies_are_rejected(self) -> None:
        config = self.project / "jonnylean.toml"
        config.write_text(config.read_text().replace(
            "depends_on = []", 'depends_on = ["JL-002"]', 1,
        ))
        result = self.cli("verify", 2)
        self.assertIn("Cyclic task dependencies", result.stderr)
        self.assertFalse((self.project / ".jonnylean.lock").exists())

    def test_review_destinations_cannot_escape_or_overwrite_source(self) -> None:
        config = self.project / "jonnylean.toml"
        original = config.read_text()
        original_source = (self.project / PARITY).read_bytes()
        external = self.project.parent / "external-review-fixture"
        external.mkdir()
        (self.project / "reviews/linked").symlink_to(external, target_is_directory=True)
        invalid = (
            "../outside.json",
            "reviews/nested/../../outside.json",
            str(external / "absolute.json"),
            str(PARITY),
            "reviews/linked/outside.json",
        )
        for destination in invalid:
            with self.subTest(destination=destination):
                config.write_text(original.replace(
                    'review = "reviews/JL-001.json"',
                    "review = " + json.dumps(destination),
                    1,
                ))
                result = self.cli("fingerprint", 2)
                self.assertIn("Review", result.stderr)
                self.assertFalse((self.project / ".jonnylean.lock").exists())
                self.assertEqual((self.project / PARITY).read_bytes(), original_source)
                self.assertEqual(list(external.iterdir()), [])
                self.assertFalse((self.project.parent / "outside.json").exists())

    def test_fingerprint_all_covers_every_task_with_the_same_source_snapshot(self) -> None:
        records = json.loads(self.cli("fingerprint", 0, "all").stdout)
        self.assertEqual({record["task"] for record in records}, {task["id"] for task in self.tasks})
        for record in records:
            self.assertEqual(record["inputs"], records[0]["inputs"])
            self.assertIn("worker.toml", record["inputs"])
            self.assertIn("tools/reporting.py", record["inputs"])

    def test_verify_all_compiles_each_contract_and_audits_all_modules(self) -> None:
        self.cli("verify", 0, "all")
        for task in self.tasks:
            with self.subTest(task=task["id"]):
                report = json.loads((self.project / "artifacts" / task["id"] / "report.json").read_text())
                self.assertEqual(report["status"], "pass")
                self.assertEqual(report["mechanical"], "pass")
                self.assertEqual(report["target"]["name"], task["declaration"])
                self.assertEqual(report["review"]["status"], "not_checked")
                self.assertEqual(set(report["audit"]["modules"]), self.modules)
                self.assertEqual(report["findings"], [])
                self.assertTrue(any(step["command"][-1] == task["contract"] for step in report["steps"]))

    def test_run_all_requires_current_review_for_every_task(self) -> None:
        self.cli("run", 1, "all")
        for task in self.tasks:
            report = json.loads((self.project / "artifacts" / task["id"] / "report.json").read_text())
            self.assertEqual(report["mechanical"], "pass")
            self.assertEqual(report["review"]["status"], "missing")
            self.synthetic_review(task["id"])
        self.cli("run", 0, "all")
        for task in self.tasks:
            report = json.loads((self.project / "artifacts" / task["id"] / "report.json").read_text())
            self.assertEqual(report["status"], "pass")
            self.assertEqual(report["review"]["status"], "approved_current")
            self.assertFalse(report["review"]["authenticated"])
            self.assertEqual(report["human_approval"], "not_recorded")
            self.assertIn("synthetic test fixture", report["review"]["reviewer"]["name"])

    def test_batch_checks_remaining_contracts_after_one_contract_failure(self) -> None:
        broken = self.tasks[2]
        contract = self.project / broken["contract"]
        contract.write_text(contract.read_text() + "\nexample : False := by sorry\n")
        self.cli("verify", 2, "all")
        for task in self.tasks:
            report = json.loads((self.project / "artifacts" / task["id"] / "report.json").read_text())
            self.assertEqual(report["status"], "error" if task["id"] == broken["id"] else "pass")
        report = json.loads((self.project / "artifacts" / broken["id"] / "report.json").read_text())
        self.assertEqual(report["steps"][-1]["command"][-1], broken["contract"])
        self.assertIn("sorry", report["steps"][-1]["output"])

    def test_dashboard_escapes_titles_and_marks_changed_inputs_stale(self) -> None:
        config = self.project / "jonnylean.toml"
        title = '<script>alert("synthetic fixture")</script> & review'
        source = config.read_text()
        original = json.dumps(self.task["title"], ensure_ascii=False)
        self.assertIn("title = " + original, source)
        config.write_text(source.replace("title = " + original, "title = " + json.dumps(title), 1))
        self.cli("verify", 0)
        dashboard = self.project / "artifacts/index.html"
        rendered = dashboard.read_text()
        self.assertIn('&lt;script&gt;alert(&quot;synthetic fixture&quot;)&lt;/script&gt; &amp; review', rendered)
        self.assertNotIn("<script>", rendered)
        self.assertIn('class="badge pass">PASS', rendered)
        spec = self.project / self.task["spec"]
        spec.write_text(spec.read_text() + "\nSynthetic fixture: a changed specification.\n")
        self.cli("dashboard", 0, "all")
        self.assertIn('class="badge stale">STALE', dashboard.read_text())
        self.assertNotIn('class="badge pass">PASS', dashboard.read_text())

    def test_dashboard_tolerates_malformed_cached_artifacts(self) -> None:
        self.report_path.parent.mkdir(parents=True)
        for malformed in ([], {"target": []}, {"review": []}, {"target": {"axioms": {}}}):
            with self.subTest(malformed=malformed):
                self.report_path.write_text(json.dumps(malformed))
                self.cli("dashboard", 0, "all")
                rendered = (self.project / "artifacts/index.html").read_text()
                self.assertEqual(rendered.count('class="badge not_run">NOT_RUN'), len(self.tasks))

    def test_dashboard_rechecks_changed_or_deleted_review_records(self) -> None:
        record = self.synthetic_review()
        self.cli("run", 0)
        dashboard = self.project / "artifacts/index.html"
        self.assertIn('class="badge pass">PASS', dashboard.read_text())
        original_criterion = record["checks"][0]["criterion"]
        record["checks"][0]["criterion"] = []
        self.write_review(record)
        self.cli("dashboard", 0, "all")
        self.assertIn('class="badge fail">FAIL', dashboard.read_text())
        self.assertIn("Review criterion names must be strings", dashboard.read_text())
        self.assertNotIn('class="badge pass">PASS', dashboard.read_text())
        record["checks"][0]["criterion"] = original_criterion
        record["decision"] = "changes_requested"
        record["findings"] = ["Synthetic fixture: review revoked after the successful run."]
        self.write_review(record)
        self.cli("dashboard", 0, "all")
        self.assertIn('class="badge fail">FAIL', dashboard.read_text())
        self.assertIn("changes_requested", dashboard.read_text())
        self.assertNotIn('class="badge pass">PASS', dashboard.read_text())
        (self.project / self.task["review"]).unlink()
        self.cli("dashboard", 0, "all")
        self.assertIn('class="badge fail">FAIL', dashboard.read_text())
        self.assertIn("missing", dashboard.read_text())
        self.assertNotIn('class="badge pass">PASS', dashboard.read_text())


if __name__ == "__main__":
    unittest.main()

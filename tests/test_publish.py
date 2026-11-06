"""Publication boundaries tested without network calls or GitHub writes."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools.publish import publish


class PublishBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="jonnylean-publish-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.body = self.root / "body.md"
        self.body.write_text("Explicit test fixture; never sent to GitHub.\n")
        self.calls = []
        self.dirty, self.branch, self.remote, self.diff, self.existing = (
            "", "codex/verified", "https://github.com/example/jonnylean.git", "JonnyLean.lean", "[]")

    def fake_invoke(self, root, command):
        self.calls.append(command)
        if command[:3] == ["git", "status", "--porcelain"]:
            return self.dirty
        if command[:3] == ["git", "branch", "--show-current"]:
            return self.branch
        if command[:3] == ["git", "remote", "get-url"]:
            return self.remote
        if command[:3] == ["git", "diff", "--name-only"]:
            return self.diff
        if command[:3] == ["gh", "pr", "list"]:
            return self.existing
        if command[:3] == ["gh", "pr", "create"]:
            return "https://github.com/example/jonnylean/pull/1"
        return ""

    def execute(self):
        with patch("tools.publish.invoke", side_effect=self.fake_invoke):
            return publish(self.root, self.body, "Synthetic fixture", "example/jonnylean", "main")

    def no_push_or_create(self):
        self.assertFalse(any(c[:2] == ["git", "push"] or c[:3] == ["gh", "pr", "create"] for c in self.calls))

    def test_dirty_tree_does_not_publish(self):
        self.dirty = " M JonnyLean.lean"
        with self.assertRaisesRegex(RuntimeError, "clean"):
            self.execute()
        self.no_push_or_create()

    def test_main_branch_does_not_publish(self):
        self.branch = "main"
        with self.assertRaisesRegex(RuntimeError, "codex/"):
            self.execute()
        self.no_push_or_create()

    def test_wrong_remote_does_not_publish(self):
        self.remote = "https://github.com/another/project.git"
        with self.assertRaisesRegex(RuntimeError, "origin"):
            self.execute()
        self.no_push_or_create()

    def test_empty_diff_does_not_push(self):
        self.diff = ""
        with self.assertRaisesRegex(RuntimeError, "No committed changes"):
            self.execute()
        self.no_push_or_create()

    def test_draft_uses_body_file_and_explicit_repo(self):
        self.assertEqual(self.execute(), "https://github.com/example/jonnylean/pull/1")
        create = next(c for c in self.calls if c[:3] == ["gh", "pr", "create"])
        self.assertIn("--draft", create)
        self.assertEqual(create[create.index("--body-file") + 1], str(self.body))
        self.assertEqual(create[create.index("--repo") + 1], "example/jonnylean")

    def test_existing_pr_is_not_duplicated(self):
        self.existing = '[{"url":"https://github.com/example/jonnylean/pull/9"}]'
        self.assertTrue(self.execute().endswith("/9"))
        self.assertFalse(any(c[:3] == ["gh", "pr", "create"] for c in self.calls))

    def test_invalid_repository_rejected_before_any_command(self):
        with patch("tools.publish.invoke") as invoke:
            with self.assertRaises(RuntimeError):
                publish(self.root, self.body, "fixture", "--bad/remote", "main")
            invoke.assert_not_called()


if __name__ == "__main__":
    unittest.main()

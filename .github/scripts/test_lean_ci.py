"""Tests for source hashing and preservation of both cached verdict colors."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import lean_ci


class VerdictTests(unittest.TestCase):
    def setUp(self):
        self.sandbox = tempfile.TemporaryDirectory()
        self.root = Path(self.sandbox.name)
        self.addCleanup(self.sandbox.cleanup)
        self.script = Path(lean_ci.__file__).resolve()
        self.env = {k: v for k, v in os.environ.items() if k != "GITHUB_OUTPUT"}

    def cli(self, *args):
        return subprocess.run([sys.executable, "-u", str(self.script), "--repo", str(self.root), *args],
                              text=True, capture_output=True, env=self.env)

    def test_success_replays_green(self):
        lean_ci.record(self.root, "abc", "success", "https://example.invalid/runs/1")
        result = self.cli("verdict", "--fingerprint", "abc")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("success", result.stdout)

    def test_failure_replays_red(self):
        lean_ci.record(self.root, "abc", "failure", "https://example.invalid/runs/2")
        result = self.cli("verdict", "--fingerprint", "abc")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("failure", result.stdout)
        inspected = self.cli("inspect", "--fingerprint", "abc")
        self.assertEqual(inspected.returncode, 0)
        self.assertIn("result=failure", inspected.stdout)

    def test_missing_corrupt_wrong_input_or_schema_never_green(self):
        for payload in [None, "bad json", "[]", json.dumps({"schema": 0}),
                        json.dumps({"schema": 1, "fingerprint": "other", "status": "success", "run_url": "u"}),
                        json.dumps({"schema": 1, "fingerprint": "abc", "status": "skipped", "run_url": "u"})]:
            with self.subTest(payload=payload):
                path = lean_ci.result_path(self.root)
                if payload is not None:
                    path.parent.mkdir(exist_ok=True)
                    path.write_text(payload)
                result = self.cli("inspect", "--fingerprint", "abc")
                self.assertEqual(result.returncode, 0)
                self.assertIn("result=miss", result.stdout)
                self.assertEqual(self.cli("verdict", "--fingerprint", "abc").returncode, 2)

    def test_force_rebuild_and_new_result(self):
        lean_ci.record(self.root, "abc", "failure", "old")
        forced = self.cli("inspect", "--fingerprint", "abc", "--force")
        self.assertEqual(forced.returncode, 0)
        self.assertIn("result=miss", forced.stdout)
        saved = self.cli("record", "--fingerprint", "abc", "--status", "success", "--run-url", "new")
        self.assertEqual(saved.returncode, 0)
        self.assertEqual(self.cli("verdict", "--fingerprint", "abc").returncode, 0)
        self.assertEqual(lean_ci.read_result(self.root, "abc")["run_url"], "new")

    def test_help_has_no_side_effects(self):
        for flag in ["-h", "--help"]:
            result = self.cli(flag)
            self.assertEqual(result.returncode, 0)
            self.assertIn("usage:", result.stdout)
        self.assertFalse(lean_ci.result_path(self.root).exists())

    def test_fingerprint_ignores_docs_but_tracks_proof_dependencies_and_ci(self):
        names = ["paper.tex", "lean/Painleve.lean", "lean/Check.lean", "lean/Painleve/A.lean",
                 "lean/lean-toolchain", "lean/lakefile.toml", "lean/lake-manifest.json",
                 ".github/workflows/lean.yml", ".github/scripts/lean_ci.py"]
        for name in names:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("original")
        with patch.object(lean_ci, "tracked_files", return_value=names):
            original = lean_ci.fingerprint(self.root)
            (self.root / "paper.tex").write_text("documentation edit")
            self.assertEqual(original, lean_ci.fingerprint(self.root))
            for name in names[1:]:
                with self.subTest(name=name):
                    (self.root / name).write_text("changed")
                    self.assertNotEqual(original, lean_ci.fingerprint(self.root))
                    (self.root / name).write_text("original")
            (self.root / "lean/Painleve/B.lean").write_text("new module")
            with patch.object(lean_ci, "tracked_files", return_value=names + ["lean/Painleve/B.lean"]):
                self.assertNotEqual(original, lean_ci.fingerprint(self.root))
            with patch.object(lean_ci, "tracked_files", return_value=[n for n in names if n != "lean/Painleve/A.lean"]):
                self.assertNotEqual(original, lean_ci.fingerprint(self.root))


if __name__ == "__main__":
    unittest.main()

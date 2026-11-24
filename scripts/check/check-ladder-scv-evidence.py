#!/usr/bin/env python3
"""Real metadata copying and production exit-trap regression; no compiler build."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / "scripts/bootstrap/capture-ladder-scv-evidence.py"
spec = importlib.util.spec_from_file_location("capture", HELPER)
capture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(capture)


class EvidenceTests(unittest.TestCase):
    def test_metadata_only_both_roots_and_exact_hashes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for family in ("build/scv", ".simple/scv"):
                snapshot = root / family / "snapshots/scv-revision-v2-fixture"
                snapshot.mkdir(parents=True)
                for name in capture.NAMES:
                    (snapshot / name).write_bytes((name + "\nsource=68bb1b5\n").encode())
                (snapshot / "source.spl").write_text("not diagnostic metadata")
            report = capture.capture(root, root / "evidence")
            self.assertEqual(len(report["files"]), 6)
            self.assertFalse(report["errors"])
            self.assertFalse(report["truncated"])
            for row in report["files"]:
                original = (root / row["path"]).read_bytes()
                self.assertEqual((root / "evidence" / row["path"]).read_bytes(), original)
                self.assertEqual(row["sha256"], hashlib.sha256(original).hexdigest())
            self.assertFalse(list((root / "evidence").rglob("*.spl")))

    def test_bounded_and_missing_metadata_is_explicit(self):
        old_bytes, old_count = capture.MAX_BYTES, capture.MAX_SNAPSHOTS
        try:
            capture.MAX_BYTES, capture.MAX_SNAPSHOTS = 4, 1
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                for name in ("a", "b"):
                    snapshot = root / "build/scv/snapshots" / name
                    snapshot.mkdir(parents=True)
                    (snapshot / capture.NAMES[0]).write_bytes(b"12345")
                report = capture.capture(root, root / "evidence")
                self.assertTrue(report["truncated"])
                self.assertEqual(report["snapshots"], 1)
                self.assertEqual(report["bytes"], 0)
                self.assertTrue(any("budget exceeded" in error for error in report["errors"]))
                self.assertTrue(any("missing" in error for error in report["errors"]))
        finally:
            capture.MAX_BYTES, capture.MAX_SNAPSHOTS = old_bytes, old_count

    def test_production_trap_keeps_exit_and_only_captures_failure(self):
        owner = (ROOT / "scripts/bootstrap/phase-ladder-step.shs").read_text()
        trap = owner[owner.index("record_ladder_exit() {"):owner.index("exe=\n")]
        shell = shutil.which("sh") or "C:/Program Files/Git/bin/bash.exe"
        for status, helper in ((0, True), (7, True), (9, False)):
            with self.subTest(status=status), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "evidence").mkdir()
                if helper:
                    destination = root / "scripts/bootstrap"
                    destination.mkdir(parents=True)
                    shutil.copyfile(HELPER, destination / HELPER.name)
                script = root / "trap.sh"
                script.write_text("set -eu\nevidence_root=$PWD/evidence\nsource_revision=fixture\n"
                                  "platform=linux-x86_64\nattempt_role=planning\nthreads=1\n"
                                  + trap + "\nexit " + str(status) + "\n", newline="\n")
                result = subprocess.run([shell, "trap.sh"], cwd=root, capture_output=True)
                self.assertEqual(result.returncode, status, result.stderr)
                self.assertIn("exit_status: " + str(status), (root / "evidence/attempt.sdn").read_text())
                self.assertEqual((root / "evidence/scv-capture.log").exists(), status != 0)
                if status == 7:
                    index = json.loads((root / "evidence/scv-failure/index.json").read_text())
                    self.assertEqual(index["admission"], "none")


if __name__ == "__main__":
    unittest.main()

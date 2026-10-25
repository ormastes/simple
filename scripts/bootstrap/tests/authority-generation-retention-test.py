#!/usr/bin/env python3
"""Exercise the canonical Rust-generation pruner on temporary fixture trees only."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
AUTHORITY = ROOT / "scripts/check/lib/bootstrap-stage3/authority.shs"
COMMAND_SNAPSHOT = ROOT / "scripts/check/lib/bootstrap-stage3/command-snapshot.shs"
WIRING = ROOT / "scripts/bootstrap/bootstrap-authority-wiring.shs"

SHELL_CALL = r'''
set -eu
portable_lock_handle_is_owned() { [ "$1" = fixture-owned-lock ]; }
. "$1"
. "$2"
. "$3"
bootstrap_authority_prune_generations "$4" "$5" fixture-owned-lock
'''


class AuthorityGenerationRetention(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="authority-generation-retention-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)

    def fixture(self, name):
        root = self.base / name
        generations = root / "generations"
        for generation in ("current", "keep-one", "keep-two", "drop-me"):
            (generations / generation).mkdir(parents=True, exist_ok=True)
            (generations / generation / "payload").write_text(generation + "\n", encoding="utf-8")
        marker = root / "current.env"
        marker.write_text("schema=fixture\ngeneration=current\n", encoding="utf-8")
        return generations, marker

    def prune(self, generations, marker, keep=None):
        env = os.environ.copy()
        if keep is None:
            env.pop("SIMPLE_BOOTSTRAP_RETAIN_GENERATIONS", None)
        else:
            env["SIMPLE_BOOTSTRAP_RETAIN_GENERATIONS"] = keep
        return subprocess.run(
            ["sh", "-c", SHELL_CALL, "retention-test", str(AUTHORITY),
             str(COMMAND_SNAPSHOT), str(WIRING), str(generations), str(marker)],
            cwd=ROOT, env=env, capture_output=True, text=True, timeout=30,
        )

    def test_default_prunes_only_noncurrent_without_keep_set(self):
        generations, marker = self.fixture("default")
        result = self.prune(generations, marker)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((generations / "current").is_dir())
        self.assertFalse((generations / "drop-me").exists())
        self.assertFalse((generations / "keep-one").exists())

    def test_explicit_set_keeps_named_physical_generations_and_prunes_others(self):
        generations, marker = self.fixture("keep")
        result = self.prune(generations, marker, "keep-one,keep-two")
        self.assertEqual(result.returncode, 0, result.stderr)
        for name in ("current", "keep-one", "keep-two"):
            self.assertTrue((generations / name).is_dir(), name)
        self.assertFalse((generations / "drop-me").exists())

    def test_invalid_sets_fail_before_any_deletion(self):
        for index, value in enumerate(("../escape", "keep-one,../escape", "keep-one,keep-one",
                                       "keep-one,", "not-present")):
            with self.subTest(value=value):
                generations, marker = self.fixture(f"invalid-{index}")
                result = self.prune(generations, marker, value)
                self.assertNotEqual(result.returncode, 0, value)
                self.assertTrue((generations / "drop-me").is_dir(), value)
                self.assertTrue((generations / "keep-one").is_dir(), value)

    def test_symlink_entry_is_rejected_before_any_deletion(self):
        generations, marker = self.fixture("symlink")
        external = self.base / "outside" / "real-generation"
        external.mkdir(parents=True)
        (generations / "linked-generation").symlink_to(external, target_is_directory=True)
        result = self.prune(generations, marker, "linked-generation")
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue((generations / "drop-me").is_dir())
        self.assertTrue(external.is_dir())

    def test_256_names_are_accepted_and_257_rejected_atomically(self):
        generations, marker = self.fixture("limit-256")
        names = [f"keep-{index}" for index in range(1, 257)]
        for name in names:
            (generations / name).mkdir()
        result = self.prune(generations, marker, ",".join(names))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((generations / "keep-256").is_dir())
        self.assertFalse((generations / "drop-me").exists())

        generations, marker = self.fixture("limit-257")
        names = [f"keep-{index}" for index in range(1, 258)]
        for name in names:
            (generations / name).mkdir()
        result = self.prune(generations, marker, ",".join(names))
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue((generations / "drop-me").is_dir())
        self.assertTrue((generations / "keep-257").is_dir())


if __name__ == "__main__":
    unittest.main()

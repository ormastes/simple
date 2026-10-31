#!/usr/bin/env python3
"""The Hello matrix strips inherited SIMPLE_* settings, but must keep the
operator's build memory reserve. Without it the compiler falls back to its
24 GiB default and refuses every build on a smaller or shared host.

Hosts: wherever CPython 3 runs (macOS, Linux, FreeBSD, Windows).
"""
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("hello_matrix", ROOT / "scripts/bootstrap/hello-sanity-matrix.py")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
KEY = "SIMPLE_BUILD_MEMORY_RESERVE_BYTES"


class ReserveTests(unittest.TestCase):
    def test_canonical_reserve_is_kept(self):
        self.assertEqual(m.inherited_build_settings({KEY: "6442450944", "SIMPLE_X": "1"}), {KEY: "6442450944"})

    def test_i64_max_reserve_is_kept(self):
        self.assertEqual(m.inherited_build_settings({KEY: "9223372036854775807"}), {KEY: "9223372036854775807"})

    def test_absent_reserve_adds_nothing(self):
        self.assertEqual(m.inherited_build_settings({"SIMPLE_X": "1"}), {})

    def test_noncanonical_reserve_refused(self):
        for value in ("", "0", "012", "-1", "6G", " 1", "9223372036854775808", "1" * 20):
            with self.assertRaises(ValueError):
                m.inherited_build_settings({KEY: value})


class LlvmBinTests(unittest.TestCase):
    def test_llvm_bin_is_sanitized(self):
        # Stage 2 resolves llc from PATH to an absolute path itself
        # (bug stage2_llc_discovery_ignores_path_2026-10-31, resolved), so the
        # matrix no longer keeps SIMPLE_LLVM_BIN across sanitization.
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(m.inherited_build_settings({"SIMPLE_LLVM_BIN": d, KEY: "1"}), {KEY: "1"})


@unittest.skipIf(os.name == "nt", "Windows drops the POSIX session contract")
class NestedSessionTests(unittest.TestCase):
    """A hello lane run by the BuildRunner worker sits inside the manager's
    watchdog session. Its own watchdog must join that session: the inherited
    contract (SIMPLE_BOOTSTRAP_SESSION_ID/EXEC) has to survive SIMPLE_*
    sanitization, and a lane with it never opens a new session."""
    SID = "SIMPLE_BOOTSTRAP_SESSION_ID"
    EXEC = "SIMPLE_BOOTSTRAP_SESSION_EXEC"

    def test_session_contract_survives_sanitization(self):
        env = {self.SID: "4242", self.EXEC: "/tmp/s/bootstrap-session-exec", "SIMPLE_X": "1"}
        self.assertEqual(m.inherited_build_settings(env),
                         {self.SID: "4242", self.EXEC: "/tmp/s/bootstrap-session-exec"})

    def test_partial_or_malformed_contract_refused(self):
        for env in ({self.SID: "4242"}, {self.EXEC: "/tmp/x"},
                    {self.SID: "0", self.EXEC: "/tmp/x"},
                    {self.SID: "12a", self.EXEC: "/tmp/x"},
                    {self.SID: "4242", self.EXEC: "relative/exec"}):
            with self.assertRaises(ValueError):
                m.inherited_build_settings(env)

    def test_nested_lane_joins_session(self):
        env = {self.SID: "4242", self.EXEC: "/tmp/s/bootstrap-session-exec"}
        self.assertTrue(m.nested_session(env, windows=False))
        self.assertFalse(m.nested_session(env, windows=True))
        self.assertFalse(m.nested_session({}, windows=False))


if __name__ == "__main__":
    unittest.main()

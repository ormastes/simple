#!/usr/bin/env python3
"""The Hello matrix strips inherited SIMPLE_* settings, but must keep the
operator's build memory reserve. Without it the compiler falls back to its
24 GiB default and refuses every build on a smaller or shared host.

Hosts: wherever CPython 3 runs (macOS, Linux, FreeBSD, Windows).
"""
import importlib.util
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
    def test_absolute_directory_is_kept(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(m.inherited_build_settings({"SIMPLE_LLVM_BIN": d}), {"SIMPLE_LLVM_BIN": d})

    def test_relative_or_missing_directory_refused(self):
        for value in ("", "bin", "/nonexistent-simple-llvm-bin-dir"):
            with self.assertRaises(ValueError):
                m.inherited_build_settings({"SIMPLE_LLVM_BIN": value})


    def test_both_settings_kept_together(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(m.inherited_build_settings({"SIMPLE_LLVM_BIN": d, KEY: "1"}),
                             {"SIMPLE_LLVM_BIN": d, KEY: "1"})

    def test_identity_records_llc_digest(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "llc").write_bytes(b"x")
            ident = m.llvm_bin_identity({"SIMPLE_LLVM_BIN": d})
            self.assertEqual(ident["llvm_bin"], d)
            self.assertEqual(len(ident["llvm_bin_llc_sha256"]), 64)
        self.assertEqual(m.llvm_bin_identity({}), {})


if __name__ == "__main__":
    unittest.main()

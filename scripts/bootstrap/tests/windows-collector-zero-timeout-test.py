#!/usr/bin/env python3
"""Real Windows Job tests for zero work deadlines; no compiler qualification."""
import ctypes
from ctypes import wintypes
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

HELPER = Path(__file__).resolve().parents[1] / "run-process-group-bounded-log-windows.py"


@unittest.skipUnless(os.name == "nt", "native Windows Job owner required")
class ZeroDeadline(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="simple-zero-deadline-")
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def argv(self, code, timeout=0, cap=4096):
        return [sys.executable, str(HELPER), "--output-parent", str(self.root),
                "--log-leaf", "child.log", "--receipt-leaf", "child.env",
                "--helper-sha256", hashlib.sha256(HELPER.read_bytes()).hexdigest(),
                "--max-bytes", str(cap), "--timeout-seconds", str(timeout),
                "--term-grace-seconds", "0", "--root-exit-policy", "terminate-job",
                "--", sys.executable, "-c", code]

    def run_owner(self, code, timeout=0, cap=4096):
        result = subprocess.run(self.argv(code, timeout, cap), capture_output=True, timeout=20)
        receipt = self.root / "child.env"
        fields = dict(line.split("=", 1) for line in receipt.read_text().splitlines()) if receipt.exists() else {}
        return result, fields

    def test_zero_deadline_reaps_root_exit_descendant(self):
        result, fields = self.run_owner(
            "import subprocess,sys; subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)']); print('root done')")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(fields["timeout_seconds"], "0")
        self.assertEqual(fields["status"], "complete")
        self.assertEqual(fields["job_remnants_terminated"], "yes")
        self.assertEqual(fields["reason"], "child-exit")

    def test_zero_deadline_still_enforces_log_bound(self):
        result, fields = self.run_owner("print('x'*10000,flush=True); import time; time.sleep(60)", cap=32)
        self.assertEqual(result.returncode, 125, result.stderr)
        self.assertEqual(fields["reason"], "overflow")
        self.assertEqual(fields["status"], "complete")
        self.assertEqual((self.root / "child.log").stat().st_size, 32)

    def test_positive_deadline_still_expires(self):
        result, fields = self.run_owner("import time; time.sleep(60)", timeout=1)
        self.assertEqual(result.returncode, 124, result.stderr)
        self.assertEqual(fields["reason"], "timeout")
        self.assertEqual(fields["status"], "complete")

    def test_negative_deadline_rejects_before_child(self):
        result, fields = self.run_owner("raise RuntimeError('must not run')", timeout=-1)
        self.assertEqual(result.returncode, 126)
        self.assertFalse(fields)
        self.assertFalse((self.root / "child.log").exists())

    def test_malformed_deadline_rejects_before_child(self):
        result, fields = self.run_owner("raise RuntimeError('must not run')", timeout="invalid")
        self.assertEqual(result.returncode, 2)
        self.assertFalse(fields)
        self.assertFalse((self.root / "child.log").exists())

    def test_interrupted_owner_closes_job_and_kills_child(self):
        marker = self.root / "child.pid"
        code = "import os,time; from pathlib import Path; Path(" + repr(str(marker)) + ").write_text(str(os.getpid())); time.sleep(60)"
        owner = subprocess.Popen(self.argv(code), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        child_handle = None
        kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        kernel.OpenProcess.restype = wintypes.HANDLE
        kernel.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
        kernel.WaitForSingleObject.restype = wintypes.DWORD
        kernel.CloseHandle.argtypes = [wintypes.HANDLE]
        try:
            deadline = time.monotonic() + 10
            while not marker.exists() and time.monotonic() < deadline:
                if owner.poll() is not None:
                    self.fail("owner exited before child marker")
                time.sleep(0.02)
            self.assertTrue(marker.exists(), "child failed to start")
            child_handle = kernel.OpenProcess(0x00100000, False, int(marker.read_text()))
            self.assertTrue(child_handle)
            owner.terminate()
            owner.communicate(timeout=10)
            self.assertEqual(kernel.WaitForSingleObject(child_handle, 10000), 0)
            self.assertFalse((self.root / "child.env").exists(), "interrupt cannot publish completion")
        finally:
            if owner.poll() is None:
                owner.kill()
                owner.communicate(timeout=10)
            if child_handle:
                kernel.CloseHandle(child_handle)


if __name__ == "__main__":
    unittest.main()

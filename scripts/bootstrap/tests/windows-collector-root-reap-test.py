#!/usr/bin/env python3
"""Bootstrap-only Win32 collector tests; no compiler or candidate execution."""
import hashlib
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HELPER = Path(__file__).resolve().parents[1] / "run-process-group-bounded-log-windows.py"
spec = importlib.util.spec_from_file_location("collector", HELPER)
collector = importlib.util.module_from_spec(spec)
spec.loader.exec_module(collector)


class RootReapTests(unittest.TestCase):
    def test_delayed_signal_uses_remaining_shared_budget(self):
        now, waits = [0.0], []
        def wait(handle, milliseconds):
            self.assertEqual(handle, 19)
            waits.append(milliseconds)
            now[0] += milliseconds / 1000
            return 0 if len(waits) == 3 else 258
        result = collector.reap_root_until(wait, 19, 10, lambda: now[0])
        self.assertEqual(result, ("reaped", 0, 0))
        self.assertEqual(waits, [1000, 1000, 1000])
        self.assertLessEqual(now[0], 10)

    def test_wait_failed_preserves_error_without_retry(self):
        calls = []
        def wait(handle, milliseconds):
            calls.append(milliseconds)
            return 0xFFFFFFFF
        self.assertEqual(collector.reap_root_until(wait, 19, 10, lambda: 0, lambda: 5),
                         ("wait-failed", 0xFFFFFFFF, 5))
        self.assertEqual(calls, [1000])

    def test_unreaped_deadline_is_finite(self):
        now, waits = [0.0], []
        def wait(handle, milliseconds):
            waits.append(milliseconds)
            now[0] += milliseconds / 1000
            return 258
        result = collector.reap_root_until(wait, 19, 2.5, lambda: now[0])
        self.assertEqual(result, ("deadline", 258, 0))
        self.assertEqual(waits, [1000, 1000, 500])
        self.assertEqual(now[0], 2.5)

    def test_expired_budget_is_failclosed_without_polling(self):
        def wait(*args):
            self.fail("expired cleanup budget must not begin another wait")
        self.assertEqual(collector.reap_root_until(wait, 19, 1, lambda: 1),
                         ("deadline", 258, 0))

    def test_unexpected_wait_cannot_prove_termination(self):
        self.assertEqual(collector.reap_root_until(lambda *_: 128, 19, 10, lambda: 0),
                         ("unexpected-wait-result", 128, 0))


@unittest.skipUnless(os.name == "nt", "actual native Windows Job required")
class WindowsReceiptTests(unittest.TestCase):
    def run_collector(self, child, limit=4096, fault=None):
        scope = tempfile.TemporaryDirectory(prefix="collector-root-reap-")
        self.addCleanup(scope.cleanup)
        parent = Path(scope.name)
        digest = hashlib.sha256(HELPER.read_bytes()).hexdigest()
        argv = ["--output-parent", str(parent), "--log-leaf", "actual.log",
                "--receipt-leaf", "actual.env", "--helper-sha256", digest,
                "--max-bytes", str(limit), "--timeout-seconds", "1",
                "--term-grace-seconds", "1", "--root-exit-policy", "wait-job",
                "--", sys.executable, "-c", child]
        prefix = [sys.executable, str(HELPER)]
        if fault:
            driver = parent / "fault-driver.py"
            # Explicit bootstrap-unit fault injection at the root-wait seam.
            driver.write_text("import importlib.util,sys\n"
                "s=importlib.util.spec_from_file_location('collector',sys.argv[1])\n"
                "m=importlib.util.module_from_spec(s);s.loader.exec_module(m)\n"
                f"m.reap_root_until=lambda *a: {fault!r}\n"
                "sys.argv=[sys.argv[1]]+sys.argv[2:];sys.exit(m.main())\n", encoding="utf-8")
            prefix = [sys.executable, str(driver), str(HELPER)]
        result = subprocess.run(prefix + argv, capture_output=True, timeout=20)
        log = (parent / "actual.log").read_bytes()
        lines = (parent / "actual.env").read_text(encoding="ascii").splitlines()
        self.assertEqual(len(lines), len({line.split("=", 1)[0] for line in lines}))
        receipt = dict(line.split("=", 1) for line in lines)
        self.assertEqual(receipt["log_sha256"], hashlib.sha256(log).hexdigest())
        self.assertEqual(int(receipt["bytes_captured"]), len(log))
        self.assertLessEqual(len(log), limit)
        self.assertEqual(receipt["helper_sha256"], digest)
        self.assertEqual(receipt["process_group"], "windows-job")
        return result, log, receipt

    def test_success_receipt_remains_complete(self):
        result, log, receipt = self.run_collector("print('actual-pass',flush=True)")
        self.assertEqual(result.returncode, 0)
        self.assertIn(b"actual-pass", log)
        self.assertEqual(receipt["status"], "complete")
        self.assertEqual(receipt["reason"], "child-exit")
        self.assertEqual(receipt["native_exit_status"], "0")

    def test_actual_timeout_preserved(self):
        result, log, receipt = self.run_collector("import time;print('timeout-evidence',flush=True);time.sleep(30)")
        self.assertEqual(result.returncode, 124)
        self.assertIn(b"timeout-evidence", log)
        self.assertEqual(receipt["status"], "complete")
        self.assertEqual(receipt["reason"], "timeout")
        self.assertEqual(receipt["cleanup_status"], "reaped")

    def test_actual_overflow_preserved(self):
        result, log, receipt = self.run_collector("import os,time;os.write(1,b'x'*8192);time.sleep(30)", 1024)
        self.assertEqual(result.returncode, 125)
        self.assertEqual(len(log), 1024)
        self.assertEqual(receipt["reason"], "overflow")
        self.assertEqual(receipt["cleanup_status"], "reaped")

    def test_wait_failed_keeps_log_and_primary_timeout_aborted(self):
        result, log, receipt = self.run_collector("import time;print('failed-reap-evidence',flush=True);time.sleep(30)",
                                               fault=("wait-failed", 0xFFFFFFFF, 5))
        self.assertEqual(result.returncode, 126)
        self.assertIn(b"failed-reap-evidence", log)
        self.assertEqual(receipt["status"], "aborted")
        self.assertEqual(receipt["reason"], "timeout")
        self.assertEqual(receipt["bound_raw_status"], "124")
        self.assertEqual(receipt["native_exit_status"], "not-run")
        self.assertEqual(receipt["cleanup_last_error"], "5")
        self.assertIn(b"bound_reason=timeout", result.stderr)

    def test_unreaped_overflow_keeps_bounded_log_aborted(self):
        result, log, receipt = self.run_collector("import os,time;os.write(1,b'x'*8192);time.sleep(30)", 1024,
                                               ("deadline", 258, 0))
        self.assertEqual(result.returncode, 126)
        self.assertEqual(len(log), 1024)
        self.assertEqual(receipt["status"], "aborted")
        self.assertEqual(receipt["reason"], "overflow")
        self.assertEqual(receipt["bound_raw_status"], "125")
        self.assertEqual(receipt["cleanup_wait_code"], "258")


if __name__ == "__main__":
    unittest.main(verbosity=2)

#!/usr/bin/env python3
"""Bootstrap-only Win32 collector tests; no compiler or candidate execution."""
import hashlib
import importlib.util
import os
import py_compile
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

HELPER = Path(__file__).resolve().parents[1] / "run-process-group-bounded-log-windows.py"
def load_module(path=HELPER):
    spec = importlib.util.spec_from_file_location("collector", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    # Execute the pinned source bytes directly: SourceFileLoader may consume
    # or create __pycache__, which mutates an immutable bootstrap checkout.
    exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
    return module


collector = load_module()


class RootReapTests(unittest.TestCase):
    def test_source_loader_preserves_metadata_without_bytecode_cache(self):
        with tempfile.TemporaryDirectory(prefix="collector-source-loader-") as scope:
            path = Path(scope) / HELPER.name
            path.write_bytes(HELPER.read_bytes() + b"\nsource_loader_witness = 917\n")
            try:
                loaded = load_module(path)
                self.assertEqual(loaded.source_loader_witness, 917)
                self.assertEqual(loaded.__file__, str(path))
                self.assertEqual(loaded.__spec__.origin, str(path))
                self.assertIs(sys.modules["collector"], loaded)
                self.assertFalse((path.parent / "__pycache__").exists())
                self.assertEqual(sorted(p.name for p in path.parent.iterdir()), [HELPER.name])
            finally:
                sys.modules["collector"] = collector

    def test_source_loader_ignores_matching_stale_bytecode(self):
        with tempfile.TemporaryDirectory(prefix="collector-stale-bytecode-") as scope:
            path = Path(scope) / HELPER.name
            path.write_bytes(HELPER.read_bytes() + b"\nsource_loader_witness = 917\n")
            stamp = path.stat()
            cache = Path(py_compile.compile(str(path), doraise=True))
            cached_bytes = cache.read_bytes()
            path.write_bytes(path.read_bytes().replace(b"source_loader_witness = 917", b"source_loader_witness = 918"))
            os.utime(path, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
            try:
                # Timestamp and length still match the cached 917 source.
                self.assertEqual(load_module(path).source_loader_witness, 918)
                self.assertEqual(cache.read_bytes(), cached_bytes)
            finally:
                sys.modules["collector"] = collector

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
                "m=importlib.util.module_from_spec(s);sys.modules[s.name]=m\n"
                "exec(compile(open(sys.argv[1],'rb').read(),sys.argv[1],'exec'),m.__dict__)\n"
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

    def test_explicit_negative_exit_is_not_evidence_of_an_exception(self):
        result, _, receipt = self.run_collector(
            "import ctypes;ctypes.windll.kernel32.ExitProcess(0xffffffff)")
        self.assertEqual(result.returncode, 125)
        self.assertEqual(receipt["status"], "complete")
        self.assertEqual(receipt["reason"], "child-native-status")
        self.assertEqual(receipt["native_exit_status"], "4294967295")
        self.assertEqual(receipt["cleanup_status"], "not-needed")

    def test_unhandled_access_violation_keeps_native_and_normalized_status(self):
        # A new OS thread executes an invalid address outside ctypes' calling
        # thread exception handler, so this is a real unhandled native fault.
        child = """import ctypes
k = ctypes.WinDLL('kernel32', use_last_error=True)
k.SetErrorMode(3)
k.CreateThread.restype = ctypes.c_void_p
h = k.CreateThread(None, 0, ctypes.c_void_p(1), None, 0, None)
if not h: raise ctypes.WinError(ctypes.get_last_error())
k.WaitForSingleObject.argtypes = [ctypes.c_void_p, ctypes.c_ulong]
k.WaitForSingleObject(h, 0xffffffff)
"""
        result, _, receipt = self.run_collector(child)
        self.assertEqual(result.returncode, 139)
        self.assertEqual(receipt["status"], "complete")
        self.assertEqual(receipt["reason"], "child-native-status")
        self.assertEqual(receipt["native_exit_status"], str(0xC0000005))
        self.assertEqual(receipt["cleanup_status"], "not-needed")

    def test_frontend_gate_preserves_neutral_native_failure_receipt(self):
        git = Path(shutil.which("git")).resolve()
        bash = git.parent.parent / "bin/bash.exe"
        self.assertTrue(bash.is_file(), "Git Bash must accompany Git")
        gate = HELPER.parents[1] / "check/cert/redeploy_gate/candidate_frontend_admission.shs"
        with tempfile.TemporaryDirectory(prefix="collector-frontend-status-") as scope:
            script = """. "$1"
CANDIDATE_FRONTEND_CAPTURE_KIND=windows-job
CANDIDATE_FRONTEND_CAPTURE_PARENT=$2
build_log=$2/probe.log
BOOTSTRAP_STAGE3_WINDOWS_COLLECTOR=$3
BOOTSTRAP_STAGE3_WINDOWS_PYTHON=$4
BOOTSTRAP_STAGE3_WINDOWS_COLLECTOR_SHA=$5
CANDIDATE_FRONTEND_MAX_LOG_BYTES=4096
COMPILER_CHECK_KILL_GRACE_SECONDS=1
COMPILER_BUILD_TIMEOUT_SECONDS=5
candidate_frontend_bounded_build p2_add "$4" -c 'import ctypes;ctypes.windll.kernel32.ExitProcess(0xffffffff)'
"""
            result = subprocess.run([str(bash), "-c", script, "collector-gate-test",
                gate.as_posix(), Path(scope).as_posix(), HELPER.as_posix(),
                Path(sys.executable).as_posix(), hashlib.sha256(HELPER.read_bytes()).hexdigest()],
                capture_output=True, timeout=20)
            # 126 would mean the receipt parser rejected the new reason.
            self.assertEqual(result.returncode, 125, result.stderr.decode(errors="replace"))
            receipt = dict(line.split("=", 1) for line in
                (Path(scope) / "probe.log.bounded.env").read_text().splitlines())
            self.assertEqual(receipt["reason"], "child-native-status")
            self.assertEqual(receipt["native_exit_status"], "4294967295")

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

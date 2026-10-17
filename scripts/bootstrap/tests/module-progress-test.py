#!/usr/bin/env python3
"""Protocol/selection/lease controls. Synthetic headers are not native proof."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
HELPER = ROOT / "scripts/bootstrap/bootstrap-module-progress.py"
spec = importlib.util.spec_from_file_location("progress", HELPER)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)

class ProgressTests(unittest.TestCase):
    def setUp(self):
        self.work = Path(tempfile.mkdtemp(prefix="module-progress-controls-"))
        self.state = self.work / "state"
        self.state.mkdir()
        self.full = self.work / "full"
        self.full.write_text("one\ntwo\nthree\nfour\nfive\n")
        self.summary = self.work / "summary"
        self.summary.touch()
        self.context = "a" * 64
        self.target = "aarch64-unknown-linux-gnu"

    def row(self, entry, result="PASS", number=183):
        row = self.work / (entry + ".row")
        log = self.work / (entry + ".log")
        log.write_text("actual fixture command terminal\n")
        obj = self.work / (entry + ".o")
        header = bytearray(20)
        header[:4] = b"\x7fELF"
        header[4:6] = bytes([2, 1])
        header[16:18] = (1).to_bytes(2, "little")
        header[18:20] = number.to_bytes(2, "little")
        obj.write_bytes(header)
        status = "0" if result == "PASS" else "1"
        row.write_text(f"task=fixture|entry={entry}|result={result}|status={status}|log={log}|artifact={obj}\n")
        return row

    def select(self, limit):
        selected = self.work / "selected"
        failed = p.select(str(self.full), str(selected), str(self.state), self.context, self.target, limit, str(self.summary))
        return selected.read_text().splitlines(), failed

    def test_advances_past_success_and_failure_then_completes_with_fail(self):
        self.assertEqual(self.select(2), (["one", "two"], False))
        p.publish(self.state, self.context, self.target, [self.row("one"), self.row("two", "FAIL")])
        self.assertEqual(self.select(2), (["three", "four"], True))
        p.publish(self.state, self.context, self.target, [self.row("three"), self.row("four")])
        self.assertEqual(self.select(2), (["five"], True))
        p.publish(self.state, self.context, self.target, [self.row("five")])
        self.assertEqual(self.select(2), ([], True))
        self.assertIn("retained_failed_count=1", self.summary.read_text())

    def test_zero_limit_selects_remaining_not_zero(self):
        p.publish(self.state, self.context, self.target, [self.row("one")])
        self.assertEqual(self.select(0)[0], ["two", "three", "four", "five"])

    def test_blocked_and_unsealed_remain_unfinished(self):
        p.publish(self.state, self.context, self.target, [self.row("one", "BLOCKED")])
        self.assertEqual(self.select(2)[0], ["one", "two"])

    def test_tampered_log_and_object_refused(self):
        row = self.row("one")
        p.publish(self.state, self.context, self.target, [row])
        (self.work / "one.o").write_bytes(b"corrupt")
        with self.assertRaises(ValueError): self.select(2)
        # A separate fresh row exercises log binding.
        p.publish(self.state, self.context, self.target, [self.row("two")])
        (self.work / "two.log").write_text("changed")
        with self.assertRaises(ValueError):
            p.load_seal(p.seal_path(self.state, "two"), self.context, "two", self.target)

    def test_wrong_context_truncated_and_duplicate_seals_refused(self):
        p.publish(self.state, self.context, self.target, [self.row("one")])
        path = p.seal_path(self.state, "one")
        with self.assertRaises(ValueError): p.load_seal(path, "b"*64, "one", self.target)
        path.write_text('{"schema":"a","schema":"b"}')
        with self.assertRaises(ValueError): self.select(2)
        path.write_text('{')
        with self.assertRaises(ValueError): self.select(2)

    def test_deep_malformed_seal_cli_refuses_stale_selection(self):
        path = p.seal_path(self.state, "one")
        path.write_text("[" * 2000 + "0" + "]" * 2000)
        stale = self.work / "selected"
        stale.write_text("old-entry\n")
        result = subprocess.run(["python3", str(HELPER), "select", str(self.full), str(stale), str(self.state), self.context, self.target, "2", str(self.summary)], capture_output=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn(b"module progress refused", result.stderr)
        # Status2 must remain rejected by the actual production status gate.
        source = (ROOT/"scripts/bootstrap/bootstrap-phase-verification.shs").read_text()
        self.assertIn('case "$module_selection_status" in 0) ;; 3) matrix_failed=1 ;; *) return 1 ;; esac', source)

    def test_arm_and_riscv_machine_identity(self):
        row = self.row("rv", number=243)
        p.machine(self.work / "rv.o", "riscv64-unknown-linux-gnu")
        with self.assertRaises(ValueError): p.machine(self.work / "rv.o", self.target)
        with self.assertRaises(ValueError): p.publish(self.state, self.context, self.target, [row])
        bad = bytearray((self.work / "rv.o").read_bytes()); bad[4] = 1
        (self.work / "rv.o").write_bytes(bad)
        with self.assertRaises(ValueError): p.machine(self.work / "rv.o", "riscv64-unknown-linux-gnu")

    def test_kernel_lock_refuses_concurrent_writer_releases_after_owner_exit(self):
        import fcntl
        lock = self.work / "writer.lock"
        fd = os.open(lock, os.O_RDWR | os.O_CREAT, 0o600)
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with lock.open("rb") as other:
            with self.assertRaises(BlockingIOError): fcntl.flock(other, fcntl.LOCK_EX | fcntl.LOCK_NB)
        os.close(fd)
        with lock.open("rb") as other: fcntl.flock(other, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def test_actual_scheduler_checkpoint_full_authority_reap(self):
        work = self.work
        script = """set -eu
. "$1/scripts/bootstrap/bootstrap-module-collection.shs"
MODULE_PROGRESS_HELPER="$1/scripts/bootstrap/bootstrap-module-progress.py"
MODULE_PROGRESS_CONTEXT="$2"
MODULE_PROGRESS_TARGET=aarch64-unknown-linux-gnu
MODULE_PROGRESS_STATE="$3/state"
export MODULE_PROGRESS_HELPER MODULE_PROGRESS_CONTEXT MODULE_PROGRESS_TARGET MODULE_PROGRESS_STATE
hash_stream() { sha256sum | awk '{print $1}'; }
validate() { [ "${MODULE_COMPILE_VALIDATE_FULL:-0}" = 1 ] && printf 'full\n' >>"$3/full-checks"; return 0; }
run() { cp "$FIXTURE_OBJECT" "$3"; printf 'fixture-reaped-command\n'; return 0; }
export FIXTURE_OBJECT
run_module_compile_inventory "$3/full" "$3/attempts" "$3/cache" 2 1 run validate "$3/summary"
"""
        self.row("fixture")
        env = dict(os.environ, FIXTURE_OBJECT=str(work/"fixture.o"))
        # validate has no positional parameters: use exported root instead.
        script = script.replace('"$3/full-checks"', '"$TEST_WORK/full-checks"')
        env["TEST_WORK"] = str(work)
        subprocess.run(["sh", "-c", script, "test", str(ROOT), self.context, str(work)], env=env, check=True, capture_output=True)
        self.assertEqual(len(list(self.state.glob("*.json"))), 5)
        self.assertEqual((work/"full-checks").read_text().splitlines(), ["full"]*3)
        self.assertEqual(self.select(2), ([], False))

if __name__ == "__main__": unittest.main()

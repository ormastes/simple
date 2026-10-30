#!/usr/bin/env python3
"""Manager/worker result-receipt controls for the BuildRunner Hello adapter.

Synthetic receipts only: these prove the parser refuses malformed or mismatched
evidence. They are not a BuildRunner Hello PASS.
"""
import hashlib
import importlib.util
import os
import shutil
import zipfile
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
HELPER = ROOT / "scripts/bootstrap/hello-sanity-buildrunner.py"
spec = importlib.util.spec_from_file_location("hello_buildrunner", HELPER)
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)

LIMIT = 1024 * 1024 * 1024
IDENTITY = "a" * 64
OUTPUT = "hello-result.zip"


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.work = Path(tempfile.mkdtemp(prefix="hello-buildrunner-receipt-"))
        self.addCleanup(shutil.rmtree, self.work, ignore_errors=True)
        self.state = self.work / "state"
        self.artifact = self.work / OUTPUT
        self.artifact.write_bytes(b"bundle bytes")
        self.digest = hashlib.sha256(b"bundle bytes").hexdigest()
        self.receipt = self.state / "receipts/hello.sdn"
        self.receipt.parent.mkdir(parents=True)

    def result_lines(self, **over):
        f = dict(header="SIMPLE-BUILD-RESULT-1", task="hello", attempt="1",
                 identity=IDENTITY, host="local-1", status="OK", exit="0",
                 hits="0", misses="1", stores="1", count="1", path=OUTPUT,
                 digest=self.digest)
        f.update(over)
        return [f[k] for k in ("header", "task", "attempt", "identity", "host",
                               "status", "exit", "hits", "misses", "stores",
                               "count", "path", "digest")]

    def write(self, lines=None, memory=None, attempt="1", host="local-1"):
        lines = self.result_lines() if lines is None else lines
        self.receipt.write_text("\n".join(lines) + "\n")
        mem = dict(format="simple-build-memory-v1", task_identity=IDENTITY,
                   requested_policy="enforce", reserved_bytes=str(LIMIT),
                   enforcement="cgroup-memory-max", enforced_bytes=str(LIMIT),
                   observed_peak_bytes="4096", peak_metric="cgroup-memory-peak")
        if memory is not None:
            mem = memory(mem)
        path = self.state / "attempts/hello" / attempt / host / "compiler.memory"
        path.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(mem, str):
            path.write_text(mem)
        else:
            path.write_text("".join(k + "=" + v + "\n" for k, v in mem.items()))
        return path

    def verify(self):
        return h.verified_memory_receipt(self.state, self.receipt, OUTPUT, self.artifact, LIMIT)

    def refuses(self, message):
        with self.assertRaises(ValueError) as caught:
            self.verify()
        self.assertEqual(str(caught.exception), message)

    # Positive control: without it every refusal below could be vacuous.
    def test_well_formed_receipt_binds_memory_evidence(self):
        memory = self.write()
        self.assertEqual(self.verify(), memory)

    def test_job_memory_enforcement_is_accepted(self):
        self.write(memory=lambda m: dict(m, enforcement="job-memory", peak_metric="job-commit-peak"))
        self.verify()

    # --- malformed result receipt ---
    def test_empty_receipt_refused(self):
        self.write(lines=[])
        self.receipt.write_text("")
        self.refuses("invalid BuildRunner result receipt")

    def test_truncated_receipt_refused(self):
        self.write(lines=self.result_lines()[:12])
        self.refuses("invalid BuildRunner result receipt")

    def test_trailing_line_refused(self):
        self.write(lines=self.result_lines() + ["extra"])
        self.refuses("invalid BuildRunner result receipt")

    def test_wrong_header_refused(self):
        self.write(lines=self.result_lines(header="SIMPLE-BUILD-RESULT-2"))
        self.refuses("invalid BuildRunner result receipt")

    def test_wrong_task_refused(self):
        self.write(lines=self.result_lines(task="other"))
        self.refuses("invalid BuildRunner result receipt")

    def test_zero_or_signed_attempt_refused(self):
        for attempt in ("0", "-1", "01", "x"):
            with self.subTest(attempt=attempt):
                self.write(lines=self.result_lines(attempt=attempt))
                self.refuses("invalid result identity")

    def test_short_or_uppercase_identity_refused(self):
        for identity in ("a" * 63, "A" * 64, "g" * 64):
            with self.subTest(identity=identity):
                self.write(lines=self.result_lines(identity=identity))
                self.refuses("invalid result identity")

    def test_unsafe_host_refused(self):
        self.write(lines=self.result_lines(host="../escape"))
        self.refuses("invalid result owner or status")

    def test_failed_status_or_nonzero_exit_refused(self):
        for over in (dict(status="FAILED"), dict(exit="1"), dict(exit="139")):
            with self.subTest(**over):
                self.write(lines=self.result_lines(**over))
                self.refuses("invalid result owner or status")

    # --- mismatched result receipt ---
    def test_output_count_mismatch_refused(self):
        self.write(lines=self.result_lines(count="2"))
        self.refuses("result does not bind the published executable")

    def test_output_path_mismatch_refused(self):
        self.write(lines=self.result_lines(path="other.zip"))
        self.refuses("result does not bind the published executable")

    def test_output_path_traversal_refused(self):
        # Positive control: test_well_formed_receipt_binds_memory_evidence binds OUTPUT.
        self.write(lines=self.result_lines(path="../hello"))
        self.refuses("result does not bind the published executable")

    def test_output_digest_mismatch_refused(self):
        self.write(lines=self.result_lines(digest="b" * 64))
        self.refuses("result does not bind the published executable")

    def test_artifact_changed_after_receipt_refused(self):
        self.write()
        self.artifact.write_bytes(b"swapped bundle")
        self.refuses("result does not bind the published executable")

    # --- worker memory receipt ---
    def test_memory_receipt_for_other_attempt_refused(self):
        self.write(attempt="2")
        self.refuses("worker memory receipt missing")

    def test_memory_receipt_for_other_host_refused(self):
        self.write(host="local-2")
        self.refuses("worker memory receipt missing")

    def test_memory_line_without_separator_refused(self):
        self.write(memory=lambda m: "format=simple-build-memory-v1\ngarbage\n")
        self.refuses("malformed worker memory receipt")

    def test_duplicate_memory_field_refused(self):
        self.write(memory=lambda m: "".join(k + "=" + v + "\n" for k, v in m.items())
                   + "observed_peak_bytes=1\n")
        self.refuses("duplicate worker memory receipt field")

    def test_missing_or_extra_memory_field_refused(self):
        def drop(m):
            m = dict(m); del m["peak_metric"]; return m
        for mutate in (drop, lambda m: dict(m, extra="1")):
            with self.subTest(mutate=mutate):
                self.write(memory=mutate)
                self.refuses("memory receipt identity or format mismatch")

    def test_memory_identity_mismatch_refused(self):
        self.write(memory=lambda m: dict(m, task_identity="c" * 64))
        self.refuses("memory receipt identity or format mismatch")

    def test_memory_format_mismatch_refused(self):
        self.write(memory=lambda m: dict(m, format="simple-build-memory-v2"))
        self.refuses("memory receipt identity or format mismatch")

    def test_unenforced_or_wrong_limit_refused(self):
        cases = (dict(requested_policy="observe"), dict(reserved_bytes=str(LIMIT - 1)),
                 dict(enforced_bytes=str(LIMIT + 1)), dict(enforcement="none"),
                 dict(enforcement="job-memory"))  # metric no longer matches
        for over in cases:
            with self.subTest(**over):
                self.write(memory=lambda m: dict(m, **over))
                self.refuses("worker did not prove the requested memory enforcement")

    def test_invalid_peak_refused(self):
        for peak in ("", "-1", "01", "1.5"):
            with self.subTest(peak=peak):
                self.write(memory=lambda m: dict(m, observed_peak_bytes=peak))
                self.refuses("invalid worker memory peak")


class BundleTests(unittest.TestCase):
    """unpack_verified_lane: worker bundle records are untrusted input."""

    EXPECTED = {"format": "hello-buildrunner-lane-v1", "lane": "one-source",
                "backend": "cranelift", "phase": 2, "compile_route": "positional",
                "compiler_sha256": "d" * 64, "status": "PASS", "admitted": "false"}

    def setUp(self):
        self.work = Path(tempfile.mkdtemp(prefix="hello-buildrunner-bundle-"))
        self.addCleanup(shutil.rmtree, self.work, ignore_errors=True)
        self.bundle = self.work / OUTPUT
        self.exe = "hello.exe" if os.name == "nt" else "hello"

    def sdn(self, fields):
        return "".join(k + ": " + (v if v in ("true", "false") else repr(v)) + "\n"
                       for k, v in fields.items())

    def write(self, lane=None, result=None, exe=b"hello bytes", extra=(), omit=()):
        lane = self.sdn(self.EXPECTED) if lane is None else lane
        if result is None:
            result = self.sdn({"status": "PASS", "phase": 2, "compiler_sha256": "d" * 64,
                               "compile_route": "positional",
                               "executable_sha256": hashlib.sha256(b"hello bytes").hexdigest()})
        with zipfile.ZipFile(self.bundle, "w") as archive:
            for name, data in (("managed-lane.sdn", lane), ("result.sdn", result), (self.exe, exe)):
                if name not in omit:
                    archive.writestr(name, data)
            for name, data in extra:
                archive.writestr(name, data)

    def unpack(self):
        return h.unpack_verified_lane(self.bundle, self.work / "verified", self.EXPECTED)

    def refuses(self, message=None):
        with self.assertRaises(ValueError) as caught:
            self.unpack()
        if message is not None:
            self.assertEqual(str(caught.exception), message)
        self.assertFalse((self.work / "verified").exists())

    def test_well_formed_bundle_extracts_executable(self):
        self.write()
        artifact = self.unpack()
        self.assertEqual(artifact.read_bytes(), b"hello bytes")

    def test_lane_identity_mismatch_refused(self):
        self.write(lane=self.sdn(dict(self.EXPECTED, backend="llvm")))
        self.refuses("managed lane identity mismatch")

    def test_failed_or_other_producer_result_refused(self):
        for over in ({"status": "FAIL"}, {"compiler_sha256": "e" * 64}, {"phase": 3}):
            with self.subTest(**over):
                fields = {"status": "PASS", "phase": 2, "compiler_sha256": "d" * 64,
                          "compile_route": "positional",
                          "executable_sha256": hashlib.sha256(b"hello bytes").hexdigest()}
                fields.update(over)
                self.write(result=self.sdn(fields))
                self.refuses("managed lane did not pass with exact producer")

    def test_executable_digest_mismatch_refused(self):
        self.write(exe=b"swapped")
        self.refuses("worker executable identity mismatch")

    def test_missing_member_refused(self):
        for name in ("managed-lane.sdn", "result.sdn", self.exe):
            with self.subTest(member=name):
                self.write(omit=(name,))
                self.refuses("worker bundle member missing")

    def test_unsafe_member_refused(self):
        self.write(extra=[("../escape", b"x")])
        self.refuses("unsafe worker bundle member")

    def test_duplicate_record_field_refused(self):
        self.write(lane=self.sdn(self.EXPECTED) + "lane: 'one-source'\n")
        self.refuses("duplicate worker evidence field")

    # Malformed records must surface as ValueError like every other refusal.
    def test_record_line_without_separator_refused(self):
        self.write(lane="garbage\n")
        self.refuses("malformed worker evidence record")

    def test_record_value_not_a_literal_refused(self):
        self.write(lane="format: (\n")
        self.refuses("malformed worker evidence record")


if __name__ == "__main__":
    unittest.main()

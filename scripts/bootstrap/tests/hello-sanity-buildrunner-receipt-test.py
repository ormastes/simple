#!/usr/bin/env python3
"""Manager/worker result-receipt controls for the BuildRunner Hello adapter.

Synthetic receipts only: these prove the parser refuses malformed or mismatched
evidence. They are not a BuildRunner Hello PASS.

Hosts: runs wherever CPython 3 runs (macOS, Linux, FreeBSD, Windows). SimpleOS
has no CPython, so this file does not run there; the Simple-side receipt
contract is covered by test/01_unit/app/bootstrap_builder/result_receipt_decode_spec.spl.
"""
import hashlib
import importlib.util
import sys
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



MONITOR_VERDICT = "functional-only BuildRunner hello (monitor policy; memory qualification deferred)"
MONITOR_CLAIM = "monitor receipt claims enforcement it did not request"
ENFORCE_REFUSAL = "worker did not prove the requested memory enforcement"


def monitor_fields(**over):
    fields = dict(format="simple-build-memory-v1", task_identity=IDENTITY,
                  requested_policy="monitor", reserved_bytes=str(LIMIT),
                  enforcement="none", enforced_bytes="0",
                  observed_peak_bytes="4096", peak_metric="process-tree-peak")
    fields.update(over)
    return fields


class MonitorReceiptTests(unittest.TestCase):
    """Opt-in functional-only mode: never a qualified memory PASS."""

    def setUp(self):
        self.work = Path(tempfile.mkdtemp(prefix="hello-buildrunner-monitor-"))
        self.addCleanup(shutil.rmtree, self.work, ignore_errors=True)
        self.state = self.work / "state"
        self.artifact = self.work / OUTPUT
        self.artifact.write_bytes(b"bundle bytes")
        self.digest = hashlib.sha256(b"bundle bytes").hexdigest()
        self.receipt = self.state / "receipts/hello.sdn"
        self.receipt.parent.mkdir(parents=True)
        self.receipt.write_text("\n".join([
            "SIMPLE-BUILD-RESULT-1", "hello", "1", IDENTITY, "local-1", "OK", "0",
            "0", "1", "1", "1", OUTPUT, self.digest]) + "\n")

    def write_memory(self, fields):
        path = self.state / "attempts/hello/1/local-1/compiler.memory"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("".join(k + "=" + v + "\n" for k, v in fields.items()))
        return path

    def verify(self, policy):
        return h.verified_memory_receipt(self.state, self.receipt, OUTPUT, self.artifact, LIMIT, policy)

    def refuses(self, policy, message):
        with self.assertRaises(ValueError) as caught:
            self.verify(policy)
        self.assertEqual(str(caught.exception), message)

    def test_monitor_receipt_accepted(self):
        # Positive control: the refusals below are meaningful only if this passes.
        memory = self.write_memory(monitor_fields())
        self.assertEqual(self.verify("monitor"), memory)

    def test_monitor_child_rss_metric_accepted(self):
        self.write_memory(monitor_fields(peak_metric="child-rss-peak"))
        self.verify("monitor")

    def test_monitor_refuses_enforcement_label_monitor(self):
        # Under monitor the enforcement value must be exactly "none".
        self.write_memory(monitor_fields(enforcement="monitor"))
        self.refuses("monitor", MONITOR_CLAIM)

    def test_monitor_refuses_non_monitor_peak_metric(self):
        for metric in ("cgroup-memory-peak", "job-commit-peak", "none", ""):
            with self.subTest(metric=metric):
                self.write_memory(monitor_fields(peak_metric=metric))
                self.refuses("monitor", "monitor receipt peak metric is not monitor-only")

    def test_monitor_refuses_enforcement_it_did_not_request(self):
        for over in (dict(enforcement="job-memory", peak_metric="job-commit-peak"),
                     dict(enforcement="cgroup-memory-max", peak_metric="cgroup-memory-peak"),
                     dict(enforcement="observe"), dict(enforced_bytes=str(LIMIT)),
                     dict(enforced_bytes="1"), dict(requested_policy="enforce")):
            with self.subTest(**over):
                self.write_memory(monitor_fields(**over))
                self.refuses("monitor", MONITOR_CLAIM)

    def test_monitor_refuses_wrong_reservation(self):
        self.write_memory(monitor_fields(reserved_bytes=str(LIMIT - 1)))
        self.refuses("monitor", "worker did not prove the requested memory monitoring")

    def test_monitor_refuses_invalid_peak(self):
        for peak in ("", "-1", "01", "1.5"):
            with self.subTest(peak=peak):
                self.write_memory(monitor_fields(observed_peak_bytes=peak))
                self.refuses("monitor", "invalid worker memory peak")

    def test_monitor_refuses_identity_and_field_drift(self):
        self.write_memory(monitor_fields(task_identity="c" * 64))
        self.refuses("monitor", "memory receipt identity or format mismatch")
        fields = monitor_fields()
        del fields["peak_metric"]
        self.write_memory(fields)
        self.refuses("monitor", "memory receipt identity or format mismatch")

    def test_enforce_refuses_monitor_receipt(self):
        # Policy mismatch, the other direction: enforce keeps its existing refusal.
        self.write_memory(monitor_fields())
        self.refuses("enforce", ENFORCE_REFUSAL)

    def test_unknown_policy_refused(self):
        self.write_memory(monitor_fields())
        with self.assertRaises(ValueError):
            self.verify("observe")


MATRIX = ROOT / "scripts/bootstrap/hello-sanity-matrix.py"
matrix_spec = importlib.util.spec_from_file_location("hello_sanity_matrix", MATRIX)
m = importlib.util.module_from_spec(matrix_spec)
matrix_spec.loader.exec_module(m)


class MatrixAggregationTests(unittest.TestCase):
    """BuildRunner summary, downgrade and exit code of the matrix."""

    def test_functional_lanes_never_summarise_as_pass(self):
        for states in ({"FUNCTIONAL"}, {"FUNCTIONAL", "UNRUN"}, {"FUNCTIONAL", "PASS"}):
            with self.subTest(states=states):
                self.assertEqual(m.buildrunner_summary(states), "FUNCTIONAL")
        self.assertEqual(m.buildrunner_summary({"FUNCTIONAL", "FAIL"}), "FAIL")

    def test_known_states_keep_their_summary(self):
        self.assertEqual(m.buildrunner_summary({"PASS"}), "PASS")
        self.assertEqual(m.buildrunner_summary({"PASS", "UNRUN"}), "PARTIAL")
        self.assertEqual(m.buildrunner_summary({"UNRUN"}), "UNRUN")
        self.assertEqual(m.buildrunner_summary({"PASS", "FAIL"}), "FAIL")

    def test_unknown_or_empty_states_are_never_pass(self):
        for states in ({"RUNNING"}, {"PASS", "SKIPPED"}, {"PASS", "weird"}, {"FUNCTIONAL", "??"}, set()):
            with self.subTest(states=states):
                self.assertNotEqual(m.buildrunner_summary(states), "PASS")

    def test_non_pass_buildrunner_downgrades_pass_to_partial(self):
        self.assertEqual(m.apply_buildrunner_status("PASS", "FUNCTIONAL"), "PARTIAL")
        self.assertEqual(m.apply_buildrunner_status("PASS", "UNRUN"), "PARTIAL")
        self.assertEqual(m.apply_buildrunner_status("PASS", "PASS"), "PASS")
        self.assertEqual(m.apply_buildrunner_status("PASS", "FAIL"), "FAIL")
        self.assertEqual(m.apply_buildrunner_status("FAIL", "PASS"), "FAIL")
        self.assertEqual(m.apply_buildrunner_status("PARTIAL", "FUNCTIONAL"), "PARTIAL")

    def test_exit_code_is_zero_only_for_pass(self):
        self.assertEqual(m.matrix_exit_code("PASS"), 0)
        for status in ("PARTIAL", "FAIL", "RUNNING_FINALIZATION"):
            with self.subTest(status=status):
                self.assertEqual(m.matrix_exit_code(status), 1)

    def test_monitor_matrix_exits_nonzero_end_to_end(self):
        for states in ({"FUNCTIONAL"}, {"FUNCTIONAL", "UNRUN"}, {"FUNCTIONAL", "PASS"}):
            with self.subTest(states=states):
                status = m.apply_buildrunner_status("PASS", m.buildrunner_summary(states))
                self.assertEqual(m.matrix_exit_code(status), 1)


class LaneStatusTests(unittest.TestCase):
    def test_only_enforce_maps_to_qualified_pass(self):
        self.assertEqual(h.lane_status("enforce"), "PASS")
        self.assertEqual(h.lane_status("monitor"), "FUNCTIONAL")
        self.assertNotIn("PASS", h.lane_status("monitor"))
        with self.assertRaises(ValueError):
            h.lane_status("observe")


class FakeMatrix:
    """Just enough matrix surface for run_lane; the manager is scripted."""

    def __init__(self, out, policy, memory):
        import types
        self.root = ROOT
        self.out = out
        self.args = types.SimpleNamespace(phase=2, compile_route="coordinator", timeout_seconds=60,
                                          max_rss_kib=LIMIT // 1024, windows_abi="msvc",
                                          memory_policy=policy, trace_stages=False,
                                          min_free_disk_bytes=0, max_log_bytes=4096)
        self.compiler = out / "compiler-input"
        self.compiler.write_bytes(b"compiler bytes")
        self.sha = h.matrix_digest(self.compiler)
        self.linker = out / "linker-input"
        self.linker.write_bytes(b"linker bytes")
        self.runtime = out / "runtime-input"
        self.runtime_hashes = {}
        self.memory = memory
        self.commands = []

    def run(self, lane, name, cmd, seconds=None):
        self.commands.append((name, list(cmd)))
        if name == "manager-run":
            self.publish(cmd)
        if name == "manager-verify":
            return b"builder: verified tasks=1\n", b""
        return b"", b""

    def check_executable(self, lane, artifact):
        return None

    def publish(self, cmd):
        state = Path(cmd[cmd.index("--state") + 1])
        published = Path(cmd[cmd.index("--output-root") + 1])
        published.mkdir(parents=True)
        lane = dict(format="hello-buildrunner-lane-v1", lane="one-source", backend="llvm",
                    phase=2, compile_route="coordinator", compiler_sha256=self.sha,
                    status="PASS", admitted="false")
        lane_sdn = "".join(k + ": " + (v if v == "false" else repr(v)) + "\n" for k, v in lane.items())
        result_sdn = ("status: 'PASS'\nphase: 2\ncompiler_sha256: %r\ncompile_route: 'coordinator'\n"
                      "executable_sha256: %r\n" % (self.sha, hashlib.sha256(b"hello bytes").hexdigest()))
        bundle = published / OUTPUT
        with zipfile.ZipFile(bundle, "w") as archive:
            archive.writestr("managed-lane.sdn", lane_sdn)
            archive.writestr("result.sdn", result_sdn)
            archive.writestr("hello", b"hello bytes")
        with bundle.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        (state / "receipts").mkdir(parents=True)
        (state / "receipts/hello.sdn").write_text("\n".join([
            "SIMPLE-BUILD-RESULT-1", "hello", "1", IDENTITY, "local-1", "OK", "0",
            "0", "1", "1", "1", OUTPUT, digest]) + "\n")
        memory = state / "attempts/hello/1/local-1/compiler.memory"
        memory.parent.mkdir(parents=True)
        memory.write_text("".join(k + "=" + v + "\n" for k, v in self.memory.items()))


def native_target():
    import platform
    machine = platform.machine().lower()
    arch = "aarch64" if machine in {"arm64", "aarch64"} else "x86_64" if machine in {"amd64", "x86_64"} else None
    if arch is None or os.name == "nt":
        return None
    if sys.platform == "darwin":
        return arch + "-apple-darwin"
    if sys.platform.startswith("linux"):
        return arch + "-unknown-linux-gnu"
    return None


class RunLaneTests(unittest.TestCase):
    """End to end through run_lane with a scripted manager and synthetic evidence."""

    def setUp(self):
        self.target = native_target()
        if self.target is None:
            self.skipTest("no native BuildRunner target for this host")
        self.work = Path(tempfile.mkdtemp(prefix="hello-buildrunner-lane-"))
        self.addCleanup(shutil.rmtree, self.work, ignore_errors=True)
        self.manager = self.work / "manager"
        self.manager.write_bytes(b"manager bytes")
        self.manifest_writer = self.work / "manifest-writer"
        self.manifest_writer.write_bytes(b"writer bytes")
        self.template = self.work / "template"
        self.template.write_bytes(b"template bytes")

    def lane(self, policy, memory):
        import contextlib
        import io
        out = self.work / ("out-" + policy)
        out.mkdir()
        matrix = FakeMatrix(out, policy, memory)
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            values = h.run_lane(matrix, "llvm", "one-source", self.manager,
                                self.manifest_writer, self.template, self.target)
        return values, buffer.getvalue(), matrix

    def test_monitor_lane_is_functional_with_exact_verdict(self):
        values, stdout, _ = self.lane("monitor", monitor_fields())
        self.assertNotIn("reason", values)
        self.assertEqual(values["status"], "FUNCTIONAL")
        self.assertNotIn("PASS", values["status"])
        self.assertEqual(values["verdict"], MONITOR_VERDICT)
        self.assertEqual(values["memory_policy"], "monitor")
        self.assertEqual(values["evidence_scope"], "functional-only-memory-deferred")
        self.assertEqual(stdout, MONITOR_VERDICT + "\n")
        self.assertNotIn("qualified", stdout)

    def test_monitor_manifest_argv_carries_policy_before_manifest(self):
        _, _, matrix = self.lane("monitor", monitor_fields())
        cmd = dict(matrix.commands)["manifest"]
        index = cmd.index("--memory-policy")
        self.assertEqual(cmd[index + 1], "monitor")
        self.assertEqual(cmd[index + 2], "--manifest")
        self.assertLess(cmd.index("--work-timeout-ms"), index)

    def test_enforce_manifest_argv_unchanged(self):
        _, _, matrix = self.lane("enforce", {
            "format": "simple-build-memory-v1", "task_identity": IDENTITY,
            "requested_policy": "enforce", "reserved_bytes": str(LIMIT),
            "enforcement": "cgroup-memory-max", "enforced_bytes": str(LIMIT),
            "observed_peak_bytes": "4096", "peak_metric": "cgroup-memory-peak"})
        cmd = dict(matrix.commands)["manifest"]
        self.assertNotIn("--memory-policy", cmd)

    def test_enforce_lane_keeps_qualified_pass_and_no_monitor_keys(self):
        values, stdout, _ = self.lane("enforce", {
            "format": "simple-build-memory-v1", "task_identity": IDENTITY,
            "requested_policy": "enforce", "reserved_bytes": str(LIMIT),
            "enforcement": "cgroup-memory-max", "enforced_bytes": str(LIMIT),
            "observed_peak_bytes": "4096", "peak_metric": "cgroup-memory-peak"})
        self.assertNotIn("reason", values)
        self.assertEqual(values["status"], "PASS")
        for key in ("verdict", "memory_policy", "evidence_scope"):
            self.assertNotIn(key, values)
        self.assertEqual(stdout, "")

    def test_enforce_lane_refuses_monitor_receipt(self):
        values, stdout, _ = self.lane("enforce", monitor_fields())
        self.assertEqual(values["status"], "FAIL")
        self.assertEqual(values["reason"], ENFORCE_REFUSAL)
        self.assertEqual(stdout, "")

    def test_monitor_lane_refuses_enforce_receipt(self):
        values, stdout, _ = self.lane("monitor", {
            "format": "simple-build-memory-v1", "task_identity": IDENTITY,
            "requested_policy": "enforce", "reserved_bytes": str(LIMIT),
            "enforcement": "cgroup-memory-max", "enforced_bytes": str(LIMIT),
            "observed_peak_bytes": "4096", "peak_metric": "cgroup-memory-peak"})
        self.assertEqual(values["status"], "FAIL")
        self.assertEqual(values["reason"], MONITOR_CLAIM)
        self.assertNotIn("verdict", values)
        self.assertEqual(stdout, "")


if __name__ == "__main__":
    unittest.main()

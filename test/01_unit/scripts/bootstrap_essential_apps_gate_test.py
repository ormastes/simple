#!/usr/bin/env python3
"""Hermetic orchestration contracts, not compiler or application qualification."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[3]
GATE = REPO / "scripts/check/check-bootstrap-essential-apps.shs"
VALIDATOR = REPO / "scripts/bootstrap/validate-test-runner-json.pl"

APP = '''#!/bin/sh
case "$0" in
 *devhub) echo 'DevHub usage';;
 *caret-native-closure) echo 'Interactive LLM chat shell';;
 *postgres_mimic_server) echo 'Usage: postgres-mimic-server';;
 *simple_web_server) echo 'simple-web-server: configuration valid';;
esac
'''
COMPILER = '''#!/bin/sh
if [ "$1" = native-build ]; then
 shift
 while [ "$#" -gt 0 ]; do
  if [ "$1" = --output ]; then shift; cp "$TEST_APP_TEMPLATE" "$1"; chmod +x "$1"; exit 0; fi
  shift
 done
 exit 8
fi
if [ "$1" = test ]; then
 passed=1
 [ "${TEST_GATE_CASE:-}" != vacuous ] || passed=0
 printf '{"success":true,"spec":{"success":true,"total_passed":%s,"total_failed":0,"total_skipped":0,"total_pending":0,"total_duration_ms":1,"groups":[],"files":[]},"spl_doctest":null,"sdoctest":null}\\n' "$passed"
 exit 0
fi
exit 9
'''

class EssentialAppsGateContracts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="essential-apps-contract-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "scripts/check").mkdir(parents=True)
        (self.root / "scripts/bootstrap").mkdir(parents=True)
        shutil.copyfile(GATE, self.root / "scripts/check/check-bootstrap-essential-apps.shs")
        shutil.copyfile(VALIDATOR, self.root / "scripts/bootstrap/validate-test-runner-json.pl")
        self.app = self.root / "app-template"
        self.app.write_text(APP)
        self.p4 = self.root / "p4"
        self.p4.write_text(COMPILER)
        self.p4.chmod(0o700)
        self.provenance = Path(str(self.p4) + ".provenance.env")
        self.provenance.write_text("test-only admission fixture; never production authority\n")
        self.core = self.root / "core.a"
        self.core.write_bytes(b"test-only archive fixture\n")
        self.out = self.root / "out"
        for name in ("db-runtime", "web-runtime", "tls"):
            (self.root / name).mkdir()
        self.env = os.environ.copy()
        self.env.pop("SIMPLE_BINARY", None)
        self.env.update(TEST_APP_TEMPLATE=str(self.app),
                        SIMPLE_DB_RUNTIME_CAPSULE=str(self.root / "db-runtime"),
                        SIMPLE_WEB_RUNTIME_PATH=str(self.root / "web-runtime"),
                        SIMPLE_WEB_TLS_SUPPLEMENT_DIR=str(self.root / "tls"))
        self.write_owner("check-post-bootstrap-stage4-sspec.shs", "echo post_bootstrap_stage4_acceptance=true\n")
        self.write_owner("check-llm-caret-native-closure.shs", 'mkdir -p "$SIMPLE_CARET_ARTIFACT_ROOT"\ncp "$TEST_APP_TEMPLATE" "$SIMPLE_CARET_ARTIFACT_ROOT/caret-native-closure"\nchmod +x "$SIMPLE_CARET_ARTIFACT_ROOT/caret-native-closure"\n')
        self.write_owner("check-caret-suite-bootstrap.shs", "echo 'STATUS: PASS test-only owner contract'\n")
        builder = 'mkdir -p "$(dirname "$2")"\ncp "$TEST_APP_TEMPLATE" "$2"\nchmod +x "$2"\n'
        self.write_owner("build-postgres-mimic-server-native.shs", 'if [ "${TEST_GATE_CASE:-}" = db-failure ]; then echo retained-db-failure; exit 42; fi\n' + builder)
        self.write_owner("build-simple-web-server-native.shs", builder)
        # Known spec targets, copied as paths only; no source/interpreter runs.
        source = GATE.read_text()
        for line in source.splitlines():
            if line.startswith("run_spec "):
                target = self.root / line.split()[2]
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("# test-only path fixture\n")
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Contract", "-c", "user.email=contract@invalid", "commit", "--allow-empty", "-qm", "fixture"], check=True)

    def write_owner(self, name, body):
        (self.root / "scripts/check" / name).write_text("#!/bin/sh\nset -eu\n" + body)

    def run_gate(self):
        return subprocess.run(["sh", str(self.root / "scripts/check/check-bootstrap-essential-apps.shs"),
                               str(self.p4), str(self.provenance), str(self.core), str(self.out)],
                              cwd=self.root, env=self.env, text=True, capture_output=True, timeout=20)

    def test_required_rows_build_artifacts_and_do_not_claim_live_gui_or_server_wire(self):
        result = self.run_gate()
        self.assertEqual(result.returncode, 0, result.stderr)
        receipt = (self.out / "result.env").read_text()
        self.assertIn("required_builds_and_suites=PASS", receipt)
        self.assertIn("live_gui=NOT_RUN", receipt)
        self.assertIn("db_server_live_request=NOT_RUN", receipt)
        self.assertIn("web_built_binary_live_request=NOT_RUN", receipt)
        rows = (self.out / "rows.tsv").read_text()
        for name in ("devhub-build", "caret-build", "db-build", "web-build", "simpledb-durability", "web-live-http", "stage4-authority-final"):
            self.assertIn(name + "\t0\t", rows)
        self.assertEqual(len((self.out / "artifacts.tsv").read_text().splitlines()), 4)

    def test_zero_examples_cannot_pass_required_spec(self):
        self.env["TEST_GATE_CASE"] = "vacuous"
        result = self.run_gate()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("invalid-or-vacuous-result", result.stderr)
        self.assertTrue((self.out / "logs/devhub-system.log").is_file())
        self.assertNotIn("status=PASS", (self.out / "result.env").read_text())

    def test_failed_builder_is_fatal_and_raw_log_survives(self):
        self.env["TEST_GATE_CASE"] = "db-failure"
        result = self.run_gate()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("db-build-exit-42", result.stderr)
        self.assertIn("retained-db-failure", (self.out / "logs/db-build.log").read_text())
        self.assertFalse((self.out / "logs/web-build.log").exists())

    def test_missing_runtime_authority_is_actionable_and_never_launches_candidate(self):
        self.env.pop("SIMPLE_DB_RUNTIME_CAPSULE")
        result = self.run_gate()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing_SIMPLE_DB_RUNTIME_CAPSULE", result.stderr)
        self.assertFalse(self.out.exists())

    def test_changed_pinned_candidate_during_owner_is_rejected(self):
        self.write_owner("check-post-bootstrap-stage4-sspec.shs", 'echo changed >> "$1"\necho post_bootstrap_stage4_acceptance=true\n')
        result = self.run_gate()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("input_identity_changed", result.stderr)
        self.assertTrue((self.out / "logs/stage4-authority.log").exists())

    def test_authority_marker_substring_does_not_pass(self):
        self.write_owner("check-post-bootstrap-stage4-sspec.shs", "echo post_bootstrap_stage4_acceptance=true-and-false\n")
        result = self.run_gate()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing-exact-positive-output", result.stderr)

    def test_real_bootstrap_insertion_runs_after_provenance_and_fails_before_acceptance(self):
        import shlex
        source = (REPO / "scripts/bootstrap/bootstrap-from-scratch.sh").read_text()
        marker = source.index("# Essential applications are required for every completed Stage 4 build.")
        start = source.rfind("stage4_verify_candidate_provenance ", 0, marker)
        end = source.index("stage3_acceptance_sanity=", marker)
        block = source[start:end]
        self.assertGreater(start, source.index("stage4_write_candidate_provenance "))
        self.assertLess(end, source.index("stage3_current_acceptance_status=verified", marker))
        self.write_owner("check-simple-core-runtime-smoke.shs", 'mkdir -p "$SIMPLE_CORE_BUILD_DIR"; printf core > "$SIMPLE_CORE_BUILD_DIR/libsimple_runtime.a"\n')
        for owner in ("build-core-c-bootstrap-runtime-capsule.shs", "build-host-gpu-runtime-capsule.shs"):
            self.write_owner(owner, 'test "$1" = --output; mkdir -p "$2"\n')
        self.write_owner("check-bootstrap-essential-apps.shs", 'echo apps >> "$TEST_TRACE"\n[ "${TEST_INSERTION_FAIL:-0}" = 0 ] || exit 42\n')
        trace = self.root / "insertion.trace"
        prefix = "set -e\n" + "repo_root=" + shlex.quote(str(self.root)) + "\n" + "full_bin=" + shlex.quote(str(self.p4)) + "\n" + "stage4_provenance=" + shlex.quote(str(self.provenance)) + "\n" + "backend=llvm; platform=aarch64-apple-darwin; jobs=1\n" + "absolute_path() { printf '%s\\n' \"$1\"; }\n" + "stage4_verify_candidate_provenance() { echo verified >> \"$TEST_TRACE\"; }\n" + "run_timeout_kill() { shift; \"$@\"; }\n" + "run_logged() { echo \"$1\" >> \"$TEST_TRACE\"; shift; \"$@\"; }\n"
        # Execute the real insertion block, replacing only its called owners.
        for fail in ("0", "1"):
            if trace.exists():
                trace.unlink()
            env = self.env.copy()
            env.update(TEST_TRACE=str(trace), TEST_INSERTION_FAIL=fail)
            result = subprocess.run(["sh", "-c", prefix + block + 'echo accepted >> "$TEST_TRACE"\n'], cwd=self.root, env=env, capture_output=True, text=True, timeout=20)
            events = trace.read_text().splitlines()
            self.assertEqual(events[:5], ["verified", "stage4-essential-simple-core", "stage4-essential-db-runtime", "stage4-essential-web-runtime", "stage4-essential-apps"])
            self.assertEqual(events[5], "apps")
            if fail == "0":
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(events[-1], "accepted")
            else:
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn("accepted", events)

if __name__ == "__main__":
    unittest.main()

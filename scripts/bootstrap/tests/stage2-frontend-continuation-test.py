#!/usr/bin/env python3
"""Closed continuation policy tests; no compiler execution or admission."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

OWNER = Path(__file__).resolve().parents[3]
CANDIDATE = '88f3c81b4a529d344cfc9459f1b3e036b6b34b49c81c1530f8d7e6af8edd8798'
PRIOR_RECORD = """
schema=simple-bootstrap-sanity-evidence-v1
status=fail
candidate_sha256_before=88f3c81b4a529d344cfc9459f1b3e036b6b34b49c81c1530f8d7e6af8edd8798
version_status=0
version_output=simple-bootstrap 1.0.0-rc.1
version_expected=1.0.0-rc.1
version_expect_status=0
version_match_status=0
unsupported_status=1
unsupported_output_sha256=373ffddd775f9bc524eb271bab164edcd7a51209a53058465cd0538c50c8d806
frontend_smoke_status=125
frontend_smoke_backend=llvm
frontend_smoke_bootstrap0_raw_status=125
frontend_smoke_bootstrap0_log_path=/c/dev/simple-fixed-seed-storage-20261024/worktree/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-sanity.env.frontend-bootstrap-0.log
frontend_smoke_bootstrap0_log_sha256=-
frontend_smoke_bootstrap0_status_path=/c/dev/simple-fixed-seed-storage-20261024/worktree/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-sanity.env.frontend-bootstrap-0.status.env
frontend_smoke_bootstrap0_status_sha256=67c84989ee89dd76734739c8f9dc84c944df06b78ada3d674310ec34e61930c1
unsupported_match_status=0
frontend_smoke_bootstrap_mode_status=0
frontend_smoke_bootstrap1_ran=false
frontend_smoke_bootstrap1_raw_status=not-run
frontend_smoke_bootstrap1_log_path=-
frontend_smoke_bootstrap1_log_sha256=-
frontend_smoke_bootstrap1_status_path=-
frontend_smoke_bootstrap1_status_sha256=-
frontend_smoke_output_sha256=ffab2af64148147383e544eb903453fe1ae8a25ff0b22bf32fff8a61334d6612
frontend_smoke_driver_log_path=/c/dev/simple-fixed-seed-storage-20261024/worktree/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-sanity.env.frontend-driver.log
frontend_smoke_driver_log_sha256=ffab2af64148147383e544eb903453fe1ae8a25ff0b22bf32fff8a61334d6612
candidate_sha256_after=88f3c81b4a529d344cfc9459f1b3e036b6b34b49c81c1530f8d7e6af8edd8798
sha_stable_status=0
checks_run=5
""".lstrip().encode()

class ContinuationPolicyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        git = shutil.which('git')
        cls.bash = Path(git).resolve().parent.parent / 'bin/bash.exe' if os.name == 'nt' else shutil.which('bash')
        if not cls.bash or not Path(cls.bash).is_file():
            raise unittest.SkipTest('Bash is required')

    def shell(self, body, *args):
        script = '''owner=$1; shift
if command -v cygpath >/dev/null 2>&1; then owner=$(cygpath -u "$owner"); fi
BOOTSTRAP_STAGE3_FACADE_PATH=$owner/scripts/check/lib/bootstrap-stage3-provenance.shs
. "$BOOTSTRAP_STAGE3_FACADE_PATH"
''' + body
        return subprocess.run([str(self.bash), '-c', script, 'continuation-policy-test',
            OWNER.as_posix(), *map(str, args)], capture_output=True, timeout=20)

    def controls(self, record=PRIOR_RECORD, candidate=CANDIDATE, version='1.0.0-rc.1'):
        with tempfile.TemporaryDirectory(prefix='frontend-controls-') as scope:
            prior = Path(scope) / 'prior.env'
            prior.write_bytes(record)
            return self.shell('''prior=$1
if command -v cygpath >/dev/null 2>&1; then prior=$(cygpath -u "$prior"); fi
bootstrap_stage3_verify_frontend_continuation_controls "$prior" "$2" "$3"
''', prior.as_posix(), candidate, version)

    def test_actual_failed_record_can_retain_only_completed_controls(self):
        self.assertEqual(hashlib.sha256(PRIOR_RECORD).hexdigest(),
            '493f783bac43335f6244e6b78632f87d7cb2d967847a90eec17e97269942d5e5')
        result = self.controls()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_candidate_and_version_mismatch_are_rejected(self):
        for candidate, version in [('0'*64, '1.0.0-rc.1'), (CANDIDATE, '9.9.9')]:
            with self.subTest(candidate=candidate, version=version):
                self.assertNotEqual(self.controls(candidate=candidate, version=version).returncode, 0)

    def test_changed_or_forged_prior_controls_are_rejected(self):
        for before, after in [(b'status=fail\n', b'status=pass\n'),
            (b'version_status=0\n', b'version_status=1\n'),
            (b'unsupported_status=1\n', b'unsupported_status=0\n'),
            (b'sha_stable_status=0\n', b'sha_stable_status=1\n'),
            (b'frontend_smoke_bootstrap1_ran=false\n', b'frontend_smoke_bootstrap1_ran=true\n')]:
            with self.subTest(field=before):
                self.assertNotEqual(self.controls(PRIOR_RECORD.replace(before, after)).returncode, 0)
        self.assertNotEqual(self.controls(PRIOR_RECORD + b'version_status=0\n').returncode, 0)

    def test_unknown_roles_and_changed_input_anchors_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix='frontend-anchor-') as scope:
            changed = Path(scope) / 'changed.txt'
            changed.write_text('untrusted replacement')
            for role in ['prior', 'source', 'runtime', 'tool', 'command', 'unknown']:
                with self.subTest(role=role):
                    result = self.shell('''path=$1
if command -v cygpath >/dev/null 2>&1; then path=$(cygpath -u "$path"); fi
bootstrap_stage3_frontend_continuation_anchor "$2" "$path"
''', changed.as_posix(), role)
                    self.assertNotEqual(result.returncode, 0)

    def test_plain_reused_control_record_cannot_claim_ordinary_admission(self):
        with tempfile.TemporaryDirectory(prefix='frontend-plain-') as scope:
            fresh = Path(scope) / 'fresh.env'
            fresh.write_text('schema=simple-bootstrap-sanity-evidence-v1\nstatus=pass\nbase_control_profile=windows-msvc-88f3-retained-controls-v1\n')
            result = self.shell('''path=$1
if command -v cygpath >/dev/null 2>&1; then path=$(cygpath -u "$path"); fi
bootstrap_stage3_verify_sanity_evidence_receipt "$path" "$path" "${path%/*}" "$path" "$owner"
''', fresh.as_posix())
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'reused controls require composed receipt', result.stderr)

    def test_pass_headers_cannot_replace_bound_frontend_artifacts(self):
        with tempfile.TemporaryDirectory(prefix='frontend-forged-pass-') as scope:
            base = Path(scope)
            (base/'prior-sanity.env').write_bytes(PRIOR_RECORD)
            (base/'candidate').write_text('untrusted candidate')
            composition = base/'continuation.env'
            composition.write_text('schema=simple-bootstrap-sanity-frontend-continuation-v1\n'
                'profile=windows-msvc-88f3-frontend-continuation-v1\nstatus=pass\n'
                'retained_checks=3\nremaining_checks=2\nchecks_run=5\n')
            result = self.shell('''base=$1
if command -v cygpath >/dev/null 2>&1; then base=$(cygpath -u "$base"); fi
bootstrap_stage3_verify_sanity_evidence_receipt "$base/continuation.env" "$base/continuation.env" "$base" "$base/candidate" "$owner"
''', base.as_posix())
            self.assertNotEqual(result.returncode, 0)

    def test_composed_input_dispatch_rejects_unbound_build_arguments(self):
        with tempfile.TemporaryDirectory(prefix='frontend-forged-args-') as scope:
            composition = Path(scope)/'continuation.env'
            composition.write_text('schema=simple-bootstrap-sanity-frontend-continuation-v1\n'
                'build_args_sha256='+'0'*64+'\n')
            result = self.shell('''path=$1
if command -v cygpath >/dev/null 2>&1; then path=$(cygpath -u "$path"); fi
bootstrap_stage3_verify_composed_sanity_input_tuple "$path" "$path" "$path" "$path" "$2"
''', composition.as_posix(), '0'*64)
            self.assertNotEqual(result.returncode, 0)

    def test_owner_closure_detects_loaded_helper_and_entrypoint_changes(self):
        with tempfile.TemporaryDirectory(prefix='frontend-owner-closure-') as scope:
            root = Path(scope)
            library = root/'scripts/check/lib'
            modules = library/'bootstrap-stage3'
            modules.mkdir(parents=True)
            shutil.copy2(OWNER/'scripts/check/lib/bootstrap-stage3-provenance.shs', library)
            for name in ['authority', 'command-snapshot', 'sanity', 'manifest-write', 'manifest-verify', 'self-test']:
                shutil.copy2(OWNER/f'scripts/check/lib/bootstrap-stage3/{name}.shs', modules)
            (root/'runner.shs').write_text('# runner fixture\n')
            (root/'frontend.shs').write_text('# frontend fixture\n')
            result = self.shell('''fixture=$1
if command -v cygpath >/dev/null 2>&1; then fixture=$(cygpath -u "$fixture"); fi
BOOTSTRAP_STAGE3_FACADE_PATH=$fixture/scripts/check/lib/bootstrap-stage3-provenance.shs
. "$BOOTSTRAP_STAGE3_FACADE_PATH"
for target in "$fixture/scripts/check/lib/bootstrap-stage3/authority.shs" "$fixture/runner.shs" "$fixture/frontend.shs"; do
    before=$(bootstrap_stage3_frontend_continuation_owner_identity "$fixture/runner.shs" "$fixture/frontend.shs") || exit 1
    printf '\\n# changed owner input\\n' >> "$target"
    after=$(bootstrap_stage3_frontend_continuation_owner_identity "$fixture/runner.shs" "$fixture/frontend.shs") || exit 1
    [ "$before" != "$after" ] || exit 1
done
''', root.as_posix())
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_unknown_candidate_is_rejected_before_any_probe_or_run_directory(self):
        with tempfile.TemporaryDirectory(prefix='frontend-no-probe-') as scope:
            base = Path(scope)
            (base/'stage2-sanity.env').write_bytes(PRIOR_RECORD)
            candidate = base/'candidate'
            candidate.write_text('#!/bin/sh\necho UNAUTHORIZED_EXECUTION\n')
            candidate.chmod(0o700)
            run = base/'new-run'
            result = self.shell('''prior=$1; candidate=$2; run=$3
if command -v cygpath >/dev/null 2>&1; then prior=$(cygpath -u "$prior"); candidate=$(cygpath -u "$candidate"); run=$(cygpath -u "$run"); fi
sh "$owner/scripts/check/run-stage2-frontend-continuation.shs" "$owner" "$owner" "$prior" "$candidate" "$run" "$prior" "$prior"
''', base.as_posix(), candidate.as_posix(), run.as_posix())
            self.assertEqual(result.returncode, 126, result.stderr)
            self.assertFalse(run.exists())
            self.assertNotIn(b'UNAUTHORIZED_EXECUTION', result.stdout + result.stderr)

    def build_thread_forwarding(self, threads):
        with tempfile.TemporaryDirectory(prefix='frontend-thread-forwarding-') as scope:
            record = Path(scope) / 'collector-args'
            result = self.shell('''. "$owner/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs"
scope=$1
if command -v cygpath >/dev/null 2>&1; then scope=$(cygpath -u "$scope"); fi
CANDIDATE_FRONTEND_CAPTURE_KIND=plain-pin
CANDIDATE_FRONTEND_CAPTURE_PARENT=$scope
CANDIDATE_FRONTEND_BUILD_THREADS=$2
build_log=$scope/probe.log
COMPILER_CHECK_KILL_GRACE_SECONDS=1
CANDIDATE_FRONTEND_MAX_LOG_BYTES=1024
candidate_frontend_collect() { printf '%s\\n' "$@" > "$scope/collector-args"; return 126; }
candidate_frontend_bounded_build p2_add candidate native-build --entry fixture.spl
''', Path(scope).as_posix(), threads)
            return result, record.read_text().splitlines() if record.exists() else []

    def test_configured_24_threads_reach_actual_bounded_build_owner(self):
        result, args = self.build_thread_forwarding('24')
        self.assertEqual(result.returncode, 126)  # Deliberate collector fixture failure.
        self.assertEqual(args[-6:], ['candidate', 'native-build', '--entry', 'fixture.spl', '--threads', '24'])

    def test_invalid_thread_counts_never_reach_collector(self):
        for threads in ['0', '00', '-1', '24garbage', '1 2']:
            with self.subTest(threads=threads):
                result, args = self.build_thread_forwarding(threads)
                self.assertEqual(result.returncode, 126)
                self.assertEqual(args, [])

if __name__ == '__main__':
    unittest.main(verbosity=2)

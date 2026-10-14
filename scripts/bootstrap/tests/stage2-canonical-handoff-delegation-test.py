#!/usr/bin/env python3
"""Exercise the real constructor handoff without a compiler or admission.

The intercepted verifier only records its environment, then exercises the
actual verifier's delegation selector and waiver rejection loop. It does not
create artifacts, receipts, seed authority, or a Phase 3 PASS.
"""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[3]
CONSTRUCTOR = ROOT / "scripts/bootstrap/bootstrap-from-scratch.sh"
VERIFIER = ROOT / "scripts/bootstrap/bootstrap-phase-verification.shs"


def section(text, start, end):
    return text.split(start, 1)[1].split(end, 1)[0]


class CanonicalHandoff(unittest.TestCase):
    def invoke(self, selection=None):
        constructor = CONSTRUCTOR.read_text()
        handoff = section(
            constructor,
            '    (\n      cd "${repo_root}" || exit 125\n'
            '      BOOTSTRAP_VERIFY_TEST_WORKERS=',
            '\n    ) >"${stage2_tests_log}"',
        )
        handoff = 'BOOTSTRAP_VERIFY_TEST_WORKERS=' + handoff
        verifier = VERIFIER.read_text()
        selector = section(verifier, '\nstage2_test_llvm_bin=""\n',
                           '\nif [ "$stage2_test_delegate" -eq 1 ]; then')
        waiver = '  for stage2_waiver_var in ' + section(
            verifier, '  for stage2_waiver_var in ', '\n  printf \'bootstrap-phase-verification:')
        with tempfile.TemporaryDirectory(prefix="stage2-handoff-unit-") as directory:
            root = Path(directory)
            script = root / "scripts/bootstrap/bootstrap-phase-verification.shs"
            script.parent.mkdir(parents=True)
            script.write_text(
                '#!/bin/sh\nset -eu\n'
                'printf "delegate=%s\\nmcdc=%s\\nworkers=%s\\nthreads=%s\\n" '
                '"${BOOTSTRAP_STAGE2_TEST_DELEGATE-unset}" "${SIMPLE_MCDC_MODE-unset}" '
                '"$BOOTSTRAP_VERIFY_TEST_WORKERS" "$BOOTSTRAP_VERIFY_BUILD_THREADS"\n'
                'die() { echo "$*" >&2; exit 2; }\n'
                'phase=stage2\nstage2_test_delegate=0\n' + selector + '\n'
                'if [ "$stage2_test_delegate" = 1 ]; then\n' + waiver + '\nfi\n'
            )
            env = dict(os.environ)
            for key in list(env):
                if key == "BOOTSTRAP_STAGE2_TEST_DELEGATE" or key.startswith("SIMPLE_MCDC_OFF_WAIVER_"):
                    env.pop(key)
            env["SIMPLE_MCDC_MODE"] = "on"
            if selection is not None:
                env["BOOTSTRAP_STAGE2_TEST_DELEGATE"] = selection
            setup = (
                'repo_root="$1"\nstage2_tests_workers=1\nstage2_tests_build_threads=2\n'
                'backend=cranelift\nstage2_admitted_absolute=unused-test-only\n'
                'stage2_tests_sha=unused-test-only\nstage2_tests_strategy=full\n'
                'stage2_tests_profile=full\nstage2_tests_work=unused-test-only\n'
                'stage2_tests_root=unused-test-only\nstage2_tests_timeout_seconds=120\n'
            )
            return subprocess.run(["sh", "-c", setup + handoff, "handoff-unit", directory],
                                  env=env, text=True, capture_output=True, timeout=5)

    def test_default_is_in_process_without_changing_mcdc(self):
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "delegate=0\nmcdc=on\nworkers=1\nthreads=2\n")

    def test_explicit_zero_stays_in_process(self):
        result = self.invoke("0")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("delegate=0\nmcdc=on\n", result.stdout)

    def test_explicit_delegation_is_preserved_and_requires_real_waiver(self):
        result = self.invoke("1")
        self.assertEqual(result.returncode, 2)
        self.assertIn("delegate=1\nmcdc=on\n", result.stdout)
        self.assertIn("need SIMPLE_MCDC_OFF_WAIVER_REASON", result.stderr)

    def test_invalid_selection_is_still_rejected_by_actual_selector(self):
        result = self.invoke("invalid")
        self.assertEqual(result.returncode, 2)
        self.assertIn("BOOTSTRAP_STAGE2_TEST_DELEGATE must be 0 or 1", result.stderr)


if __name__ == "__main__":
    unittest.main()

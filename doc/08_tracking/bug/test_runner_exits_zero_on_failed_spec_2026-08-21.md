# `bin/simple test` exits 0 while its own verdict reports failed=1

**Status:** OPEN (observation only — not root-caused here)
**Found:** 2026-08-21
**Reporter:** networking fragment-accumulator lane

## Observation

A spec run that reported a real failure in its own verdict lines still exited
with status 0. Exit status is therefore not a usable pass signal for
`bin/simple test`, and a caller gating on `$?` alone gets a false green.

Exact command (from repo root, binary
`bin/release/x86_64-unknown-linux-gnu/simple`, the Rust bootstrap seed):

```
bin/simple test test/01_unit/os/apps/sshd/ssh_sftp_v3_spec.spl
```

Exact output lines:

```
  ✗ rejects traversal without filesystem access
    semantic: class `SshStringResult` has no field named `value`
7 examples, 1 failure
SPEC FILE VERDICT: test/01_unit/os/apps/sshd/ssh_sftp_v3_spec.spl outcome=OK declared>=9 executed=9 passed=8 failed=1 skipped=0 dropped=0
spec failure: 1 of 9 example(s) failed (exit 1)
error: test-runner: spec failed
Results: 9 total, 8 passed, 1 failed
FAIL test/01_unit/os/apps/sshd/ssh_sftp_v3_spec.spl
```

Exit status: **0**.

Note the internal inconsistency inside a single run: the runner prints
`spec failure: 1 of 9 example(s) failed (exit 1)` and `FAIL`, yet
`SPEC FILE VERDICT` on the same run says `outcome=OK` despite carrying
`failed=1` in the same line. The `outcome=OK` field and the process exit
status agree with each other and disagree with `failed=1`, so the defect
looks like the failure count never reaching whatever computes `outcome` and
the final status.

## Why this matters

This is a fail-open in the gate that everything else is verified through. The
failure it hid in this instance was real and security-relevant: the SFTP
path-traversal guard had never compiled
(`doc/08_tracking/bug/simpleos_sftp_fragment_accumulator_quadratic_2026-08-20.md`).

## Reliable signal until fixed

Read the `Results:` / `SPEC FILE VERDICT` line and check `failed=`; do not
gate on `$?`.

## Note

Believed to be the same fail-open as the test-tracker finalization defect
another agent is root-causing. Recorded independently so the observation is
not lost; no fix attempted here.

## Fix (2026-08-21)

The invariant `failed > 0 => non-OK outcome => non-zero exit` is now enforced in
one place per lane, not patched per symptom:

- **Rust seed** `src/compiler_rust/driver/src/cli/basic.rs`,
  `report_spec_file_verdict`: `SpecOutcome::Ok` means only "the module ran to
  completion" and is decided BEFORE the BDD table is tallied, which is exactly
  how `outcome=OK ... failed=1` was printed and how a clean module status
  exited 0 over a failed example. Immediately after `failed` is computed, an
  `Ok` outcome with `failed > 0` is downgraded to `Error` and a zero
  `module_exit_code` is raised to 1. Both the printed token and the returned
  status derive from those same two values, so they cannot disagree again.
  **Not executed-verified here:** proving it needs a seed rebuild, and the host
  is at 100% disk with a bootstrap running. Source fix only, stated as such.
- **Pure-Simple aggregate lane** `src/app/test_daemon/light_protocol.spl`: new
  `verdict_outcome_token(executed, failed)` is the single derivation —
  `failed > 0` is never OK, `executed == 0` is never OK — and
  `ran_verdict_line` now carries `outcome=`. That lane previously emitted
  verdict lines with no outcome token at all.

Reproduce spec: `test/01_unit/app/test_daemon/spec_verdict_invariant_spec.spl`
(4 examples). Pre-fix it cannot pass — `verdict_outcome_token` did not exist and
`ran_verdict_line` emitted no `outcome=` field. Post-fix:
`Results: 4 total, 4 passed, 0 failed`. It also covers the vacuous case
(`executed == 0` must be NOT_RUN, never OK) and pins the outcome->exit mapping.

Same fail-open family as `SdnTable::update_row`'s discarded bool — see
`doc/08_tracking/bug/test_db_update_row_keys_nonexistent_id_column_2026-08-21.md`.

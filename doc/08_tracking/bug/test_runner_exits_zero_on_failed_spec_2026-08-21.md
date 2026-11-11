# `bin/simple test` exits 0 while its own verdict reports failed=1
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED (2026-08-21 fix; 2026-11-11 runner10 lane verified the seed binary contains the Rust half and the reproduce spec covers the pure-Simple half)
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


## 2026-11-11 — runner10 lane verdict: FIXED (both lanes verified in-tree)

Re-verified fresh at base 79d5af6723f6 (no re-runs of prior checks):

1. **Rust seed half — in the tracked binary.** The doc's own 2026-08-21 fix
   note said "proving it needs a seed rebuild". The tracked seed
   `bin/simple.exe` is now at commit 46fe8f6b6def, and
   `git show 46fe8f6b6def:src/compiler_rust/driver/src/cli/basic.rs`
   contains the invariant at lines 292-307: `failed > 0 &&
   outcome == SpecOutcome::Ok` downgrades to `SpecOutcome::Error` and a zero
   `module_exit_code` is raised to 1, in `report_spec_file_verdict` — the
   single-derivation fix this row specified. The deployed binary post-dates
   the fix.
2. **Pure-Simple half — live from source.** `verdict_outcome_token` /
   `ran_verdict_line` (`src/app/test_daemon/light_protocol.spl`) and the
   reproduce spec `test/01_unit/app/test_daemon/spec_verdict_invariant_spec.spl`
   (4 examples: failed>0 never OK, executed==0 never OK, clean file still
   OK, failing outcome maps to exit 1) are both tracked at this base; the
   pure-Simple runner runs from source under the seed, so the spec is the
   live regression gate.

Caveat: the reproduce spec was NOT re-executed this lane (session died
mid-flight; campaign no-rerun rule) — the flip rests on seed-ancestry
verification for the Rust half plus in-tree presence of the pure-Simple
gate. Related but distinct known-live route (inverse polarity: "bin/simple
test exits 1 with verdict OK — seed lane", child exit plumbing) is owned by
the seed lane and is NOT this row.

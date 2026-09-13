# Stage 4 test runner loses bounded child output and status

- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
- **Candidate:** `00431ce52f940722f52746a802011f7d33f35d4931738facee26c5c7b7917b31`.

## Reproduction

Running `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl` directly
through the candidate emits 67,891 bytes and the real footer
`16 examples, 2 failures`. Running the same file through `simple test` records
an empty child result with exit zero, then correctly fails closed with
`no parseable pass/fail summary`.

## Diagnosis

The summary parser already accepts singular and plural BDD footers. The loss is
before parsing on the limited bounded-result path:
`process_run_with_limits_bounded` -> `rt_process_run_bounded` ->
`ProcessResult`. Current evidence does not isolate which boundary corrupts the
result, so a direct tuple-only root claim would be premature. This is not a
parser defect.

## Required repair

Add one native admission probe whose child writes distinct stdout and stderr
markers and exits nonzero. Exercise the no-limits tuple path and the limited
`ProcessResult` path separately, then repair the first boundary that diverges.
Keep the existing fail-closed summary behavior; missing evidence must never
become a synthetic pass.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.

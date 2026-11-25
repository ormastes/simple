# Stage 4 test runner loses bounded child output and status

- **Status:** OPEN / CANDIDATE REJECTED.
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

## Triage 2026-11-25 (release/1.0.0 @ 64dfa6d980f, Windows host)

Still OPEN; no change made. Notes for the next lane:

- The required repair (a native admission probe exercising the no-limits
  tuple path and the limited `ProcessResult` path separately, then fixing
  the first diverging boundary) touches the Rust-seed bounded-capture
  boundary and needs a native/bootstrap build — out of scope on this host.
- Related work landed 2026-11-15: `da60e2106d1` ("feat(process): retain
  bounded capture completion evidence", PR #9520) reworked the pure-Simple
  bounded path in `src/lib/nogc_sync_mut/io/process_ops.spl` and added
  native evidence specs (`process_capture_evidence_{linux,windows}_native_v1_spec.spl`).
  Whether it resolves the stage4 symptom (`simple test` on
  `stage4_smoke_gate_spec.spl` recording an empty child result) is unverified.
- Verification on this host is blocked twice over: `bin/simple.exe test`
  fails repo-wide at HEAD with `unknown decorator '@representation_boundary'`,
  and `src/lib/nogc_sync_mut/io/process_ops.spl` itself carries 81 such
  annotations, so even a `run`-lane probe of the bounded API cannot load.

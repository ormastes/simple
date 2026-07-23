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

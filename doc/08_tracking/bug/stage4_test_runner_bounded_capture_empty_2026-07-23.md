# Stage 4 test runner loses bounded child output and status

- **Status:** ROOT FIX WRITTEN AND C-LEVEL REGRESSION PASS / FRESH STAGE 4 PENDING.
- **Candidate:** `00431ce52f940722f52746a802011f7d33f35d4931738facee26c5c7b7917b31`.

## Reproduction

Running `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl` directly
through the candidate emits 67,891 bytes and the real footer
`16 examples, 2 failures`. Running the same file through `simple test` records
an empty child result with exit zero, then correctly fails closed with
`no parseable pass/fail summary`.

## Diagnosis

The summary parser already accepts singular and plural BDD footers. GDB on a
fresh incremental full CLI proved that the process tuple reaches
`make_result_from_output` intact, but stdout contains only 61,723 of the direct
run's 67,891 bytes; the missing suffix contains the BDD footer.

The loss is in `rt_fork_parent_wait_bounded`: after the directly tracked
delegate exits, 40 empty 50ms polls trigger descendant cleanup even when the
caller supplied a longer overall deadline. A delegated seed may compute
silently for more than two seconds before emitting its remaining tests and
footer, so the bridge kills it early and reports the already-reaped parent's
zero status.

## Required repair

Positive-timeout waits now rely on their existing `deadline_ms`; the short
post-parent grace cap remains only for unbounded waits. A standalone harness
against the real `runtime_fork.c` API holds inherited stdout/stderr pipes silent
for three seconds, then writes distinct markers. It passes with exact streams,
zero status, and no timeout (`fork-deadline-ok`). The regular bounded-output
contract now carries the same regression plus a two-stream/nonzero-status case.

A fresh Stage 4 candidate still must run the focused test-runner reproduction.
Keep the existing fail-closed summary behavior; missing evidence must never
become a synthetic pass.

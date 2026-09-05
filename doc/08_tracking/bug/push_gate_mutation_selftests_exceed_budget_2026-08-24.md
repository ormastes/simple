# Push gate reruns bootstrap mutation suites and exceeds its budget

Status: fixed and verified

## Evidence

The production push path is recorded at 11.05 seconds and 225,736 KiB in
`doc/05_design/must_check_tiering.md`, exceeding the approximately ten-second
NFR by 1.05 seconds. Two push-tier registry rows invoke their guards without a
scan-only mode:

- `push-interpreter-extern-registry-gap`; and
- `push-type-walk-constructor-parity`.

Both default commands execute mutation fixtures before scanning the real tree.
Those fixtures are correctness evidence for the guard implementation, not a
property of the outgoing commit, and belong in the bootstrap tier.

## Acceptance

- Production push rows invoke scan-only modes.
- Mutation self-tests remain mandatory automated bootstrap rows.
- Default manual guard execution still runs self-tests before the real scan.
- Focused fixtures prove the registry split and both scan-only commands.
- The same production push timing measurement is compared after the change.

## Current verification

The focused must-check tiering contract passed once after the split, reporting
`ref-path=1s`; the complete fixture suite took 11.39 seconds with 6,656 KiB
peak RSS. Independent review confirmed identical 47-row bootstrap manifest and
ledger order, mandatory self-test retention, and fail-closed scan-only paths.
The historical production result remains the authoritative NFR value until this
change is committed and the same committed-ref measurement is repeated.

The first committed-ref measurement exposed a closed-dispatch mismatch: the
manifest named the new commands but the push consumer still allowlisted the old
command strings. It failed closed in 4.38 seconds at 230,016 KiB. The dispatcher
now matches and forwards both `--scan-only` arguments; the focused contract pins
that manifest/dispatcher coupling before the production measurement is retried.

The corrected exact committed-ref path passes in 4.57 seconds at 227,920 KiB
peak RSS. Compared with the retained 11.05-second/225,736-KiB baseline, elapsed
time fell 58.6% while peak RSS increased 0.97%. Both real scans report nonzero
counts (282 extern symbols and 11 type constructors); no coverage was replaced
with a vacuous timing shortcut.

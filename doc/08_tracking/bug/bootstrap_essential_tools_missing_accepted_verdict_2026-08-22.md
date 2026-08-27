# Bootstrap essential-tools gate omits accepted final verdict

Status: RESOLVED — `codex/session-01a023a8`

## Failure

`check-bootstrap-essential-tools-smoke.shs` returned zero after printing
`bootstrap_essential_tools_smoke=true`, but the bootstrap ledger accepts an
automated row only when its final non-empty line contains a standalone `PASS`.
The bootstrap validator therefore classified a successful essential-tools run
as `exit 0 without accepted PASS`.

## Resolution

Keep the machine-readable smoke marker and finish with an explicit accepted
`PASS` verdict. This changes no tool behavior and makes the producer conform to
the existing fail-closed ledger contract.

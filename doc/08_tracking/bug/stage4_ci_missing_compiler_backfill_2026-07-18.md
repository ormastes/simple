# Stage4 full-CLI CI omitted compiler backfill
## Closed 2026-09-16 — ...Cargo cache retained stale output. ## Fix and prevention The LLVM seed step now builds `si

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Symptom

The Linux LLVM workflow selected `--full-cli`, but its seed build produced only
the driver and native-all archives. A cold runner therefore lacked the required
`simple-compiler-backfill` archive and could accidentally appear green only
when a Cargo cache retained stale output.

## Fix and prevention

The LLVM seed step now builds `simple-compiler-backfill` before any full-CLI
bootstrap selection. The bootstrap source regression reads the workflow and
requires that prerequisite to occur before `mcp_flag=--full-cli`.

This is source/static evidence only; the workflow has not been executed in this
session.


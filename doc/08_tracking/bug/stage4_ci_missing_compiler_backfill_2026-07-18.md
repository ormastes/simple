# Stage4 full-CLI CI omitted compiler backfill

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

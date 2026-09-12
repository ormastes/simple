# Stage4 full-CLI CI omitted compiler backfill

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.

# Rust Async Process Unread-Pipe Hang
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Status

Fixed in source on 2026-07-17 for both the native SFFI and interpreter owners.

## Reproduction

`rt_process_spawn_async` configured stdout and stderr as pipes, returned only a
PID, and exposed no API that drained either pipe. A child that wrote more than
the platform pipe capacity could block before exit, so bounded polling never
observed completion and the caller appeared hung.

## Fix and Prevention

Both Rust owners now inherit stdout and stderr, matching the C owner and the
PID-only API contract. The test-runner source contract requires inherited
streams in both implementations. The lifecycle unit tests also require a timed
wait to retain the child and a subsequent kill to reap it.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

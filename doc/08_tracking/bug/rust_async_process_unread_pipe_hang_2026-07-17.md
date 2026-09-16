# Rust Async Process Unread-Pipe Hang
## Closed 2026-09-16 — Status: Fixed in source 2026-07-17 for native SFFI and interpreter owners

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

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


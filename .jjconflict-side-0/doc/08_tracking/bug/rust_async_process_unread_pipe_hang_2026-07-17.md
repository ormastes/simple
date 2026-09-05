# Rust Async Process Unread-Pipe Hang

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

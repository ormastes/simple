# Test-runner native signal exit status tag corruption — 2026-07-24

**Status:** OPEN / ROOT IS BELOW TEST RUNNER

## Reproduction

Running the focused phase-2 spec through the deployed pure-Simple test runner
failed with:

```text
Error: Process exited with code 2305843009213693951
```

The direct child emitted parser errors and then SIGILL. Evidence:

- `build/mini_builds/duplicate-incremental-phase2-current-interpreter.log`
- `build/mini_builds/duplicate-incremental-phase2-current-direct.log`

`2305843009213693951` is `0x1fffffffffffffff`, the documented masked/tagged
representation seen when a negative native integer or nil sentinel crosses the
wrong ABI path.

## Root cause boundary

The runner does not manufacture this value. `process_run_bounded` returns the
corrupted exit field and `make_result_from_structured_evidence` reports it
verbatim. Existing bounded-process tests cover positive exit 17, spawn failure,
and timeout, but do not prove a native signal/negative-status round trip.

Do not map this sentinel to a friendly runner error. That would hide the actual
compiler/runtime crash and leave every other `process_run_bounded` caller
corrupted.

## Required solution

Fix signed i64/tuple-field preservation at the native process-result ABI owner.
Add one native-vs-interpreter regression that runs a child terminated by a
signal and requires a stable documented negative/signal status. The formatted
result must never expose `0x1fffffffffffffff`. Then qualify the normal
test-runner failure path once with a fresh admitted Stage-4 binary.

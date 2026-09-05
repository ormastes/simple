# Native array iteration/indexing fails in async-driver smoke

Date: 2026-05-13
Status: Fixed (verified 2026-05-19 — both symptoms resolved in current HEAD)
Area: native codegen, arrays, webserver perf validation

## Summary

While validating `test/05_perf/webserver/async_driver_native_smoke.spl`, the native async-driver FFI path successfully created a driver, submitted a timeout, flushed, and returned one completion from `rt_driver_poll`.

Two native-only array access forms prevented using the fuller smoke as written:

- Iterating `for completion in completions` never observed the returned completion.
- Directly checking `completions[0].id` segfaulted in `spl_main`.

The smoke was narrowed to `completions.len() > 0` so it validates the async-driver runtime path without masking the separate array bug.

## Reproduction

```bash
src/compiler_rust/target/debug/simple compile test/05_perf/webserver/async_driver_native_smoke.spl --native --cpu native --opt-level aggressive -o build/perf/webserver/async_driver_native_smoke
build/perf/webserver/async_driver_native_smoke
```

Temporary diagnostic variants:

- A `for completion in completions` loop reports no matching completion even though `rt_driver_poll` returns `1`.
- A `completions[0].id` check crashes with `SIGSEGV` in `spl_main`.

## Expected

Native array iteration and indexed field access over `[Completion]` should observe the same completion data returned by `IoDriver.poll`.

## Impact

This blocks richer native webserver smoke tests that inspect completion IDs and payloads. It does not block the narrower async-driver runtime smoke, but it must be fixed before claiming production-level native async HTTP behavior.

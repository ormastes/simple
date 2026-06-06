# Green Thread Direct Runtime Blockers

Date: 2026-06-06

## Summary

Direct green-thread perf checks exposed runtime/compiler blockers that are
separate from the cooperative queue semantics:

- Direct interpreter/SMF function-value calls can segfault:
  `fn call(cb: fn() -> i64) -> i64: cb()`.
- Direct interpreter global array append/index can segfault after mutation.
- SMF mutable globals can segfault even for a minimal counter:
  `var COUNT: usize = 0; COUNT = COUNT + 1`.

## Impact

`green_spawn(fn)` remains covered by the SPipe unit runner, but direct perf
scripts cannot use the closure path as a reliable benchmark input yet.
`green_spawn_value(result)` is used for direct perf checks to exercise the
cooperative queue without function-value calls or global array mutation.

Green threads also cannot be used as proof of C/Go parity for CPU-parallel
workloads because they run on the current OS thread. On 2026-06-06, the existing
cross-language harness with `WORKERS=2 GREEN_WORKERS=2 RUNS=3` measured:

- Simple green native: 9.479 ms
- C pthreads: 5.852 ms
- Go goroutines/channels: 6.117 ms

This is a model mismatch, not just a local queue optimization issue. Use
`thread_spawn`/pool-backed native work for C/Go-style CPU parallelism once the
native OS-thread path compiles and runs cleanly.

## Reproduction

Temporary local repro files were created under `build/tmp/` while investigating:

- `fn_param_min.spl`
- `global_array_append_smoke.spl`
- `global_usize_smoke.spl`

## Required Fix

Fix direct interpreter and SMF handling for function-value calls and mutable
global state, then switch the perf harness green row back to `green_spawn(fn)`
for closure execution timing.

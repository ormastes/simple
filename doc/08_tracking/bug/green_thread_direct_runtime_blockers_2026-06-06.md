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

2026-06-06 follow-up: a Pure Simple delayed-closure queue was prototyped by
storing `fn() -> i64` values and running them from `green_run_one()`. Interpreter
checks and SPipe examples passed, but native entry-closure evidence failed:

- Array-backed function storage compiled, then the native smoke segfaulted with
  `exit=139`.
- Fixed function-valued global slots compiled, but native codegen emitted
  `CODEGEN-WARN ... IncompatibleDeclaration` for `GREEN_TASK_FUNC_*`, and the
  native smoke again segfaulted with `exit=139`.

Until native codegen can safely store and call function-valued globals or array
entries, `green_spawn(fn)` must keep the native-safe eager-result behavior and
`green_spawn_value(result)` remains the stable profile harness input.

Green threads also cannot be used as proof of C/Go parity for CPU-parallel
workloads because they run on the current OS thread. On 2026-06-06, the existing
cross-language harness with `WORKERS=2 GREEN_WORKERS=2 RUNS=3` measured:

- Simple cooperative green native: 9.479 ms
- C pthreads: 5.852 ms
- Go goroutines/channels: 6.117 ms

This is a model mismatch, not just a local queue optimization issue. Use
`thread_spawn` or pool-backed native work for C/Go-style CPU parallelism. Do not
use `thread_spawn_with_args` as native performance evidence until
`doc/08_tracking/bug/native_thread_spawn_with_args_abi_2026-06-06.md` is fixed.

The cross-language harness now reports Simple OS-thread and Simple cooperative
green rows separately. A 20-worker OS-thread fanout smoke compiles and runs
through unrolled `thread_spawn` fork-join handles. `thread_spawn_with_args`
native probes currently segfault with exit 139 even when handles are joined, so
that explicit-argument path is tracked as a separate ABI blocker. The remaining
direct-run blockers are the cooperative green SMF mutable-global failure,
native/SMF function-valued storage/codegen failures, and the
`thread_spawn_with_args` native ABI issue; those are runtime/compiler issues,
not public API change requests.

## Multicore Green SMF Fanout Blocker

The native `multicore_green_spawn` path has separate runtime-pool evidence:
`test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` exits nonzero if
any handle reports `used_runtime_pool() == false`. Current native evidence
passes that gate.

The SMF fanout row remains a runtime blocker, not M:N evidence. The current
cross-language smoke report (`doc/09_report/cross_language_perf_parallel_smoke.md`)
classifies:

- `Simple multicore green (SMF)` parallel CPU workers as
  `multicore_green runtime pool candidate (checksum mismatch)`. The row now
  exits nonzero because generated Simple concurrency workloads compare joined
  results against a sequential expected checksum.
- `Simple multicore green (SMF)` large fanout as
  `multicore_green runtime pool fanout (segfault)`.

Keep SMF multicore-green failures classified separately from native M:N evidence
until the SMF runtime can execute the generated `fanout_multicore_green.spl`
workload without segfaulting, execute the generated `parallel_multicore_green.spl`
workload without checksum mismatch, and report `used_runtime_pool()` for every
handle.

## Reproduction

Temporary local repro files were created under `build/tmp/` while investigating:

- `fn_param_min.spl`
- `global_array_append_smoke.spl`
- `global_usize_smoke.spl`

## Required Fix

Fix native and SMF handling for function-valued globals/arrays and mutable
global state, then switch or add a perf harness green row for delayed
`green_spawn(fn)` closure execution timing.

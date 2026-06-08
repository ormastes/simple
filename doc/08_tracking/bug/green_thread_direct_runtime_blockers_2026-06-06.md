# Green Thread Direct Runtime Blockers

Date: 2026-06-06

## Summary

Direct green-thread perf checks exposed runtime/compiler blockers that are
separate from the cooperative queue semantics:

- Direct/native function-parameter callbacks previously segfaulted for
  `fn call(cb: fn() -> i64) -> i64: cb()`. Fixed on 2026-06-08 by
  materializing top-level function values as closure objects before parameter
  passing.
- Direct interpreter global array append/index can segfault after mutation.
- SMF mutable globals can segfault even for a minimal counter:
  `var COUNT: usize = 0; COUNT = COUNT + 1`.

## Impact

`green_spawn(fn)` is covered by the SPipe unit runner and now has focused native
callback smoke coverage through
`test/05_perf/profile_scripts/native_function_value_callback_regression_test.shs`.
Direct perf scripts still use `green_spawn_value(result)` where they need to
avoid delayed function storage and isolate cooperative queue overhead.

2026-06-06 follow-up: a Pure Simple delayed-closure queue was prototyped by
storing `fn() -> i64` values and running them from `green_run_one()`. Interpreter
checks and SPipe examples passed, but native entry-closure evidence failed:

- Array-backed function storage compiled, then the native smoke segfaulted with
  `exit=139`.
- Fixed function-valued global slots compiled, but native codegen emitted
  `CODEGEN-WARN ... IncompatibleDeclaration` for `GREEN_TASK_FUNC_*`, and the
  native smoke again segfaulted with `exit=139`.

Until native codegen can safely store and call function-valued globals or array
entries, `green_spawn(fn)` must keep the native-safe eager-result behavior.
`green_spawn_value(result)` remains the stable profile harness input for direct
queue/fanout timing.

Green threads also cannot be used as proof of C/Go parity for CPU-parallel
workloads because they run on the current OS thread. On 2026-06-06, the existing
cross-language harness with `WORKERS=2 GREEN_WORKERS=2 RUNS=3` measured:

- Simple cooperative green native: 9.479 ms
- C pthreads: 5.852 ms
- Go goroutines/channels: 6.117 ms

This is a model mismatch, not just a local queue optimization issue. Use
`thread_spawn` or pool-backed native work for C/Go-style CPU parallelism.
`thread_spawn_with_args` is now covered by
`scripts/check/check-thread-spawn-with-args-native.shs`, but profile rows keep
using `thread_spawn` so the OS-thread scheduler baseline is not mixed with
explicit-argument ABI smoke coverage.

2026-06-08 follow-up: native top-level function values passed as parameters now
run through a uniform closure-object representation. Minimal direct/native
evidence:

- `fn call(cb: fn() -> i64) -> i64: cb()` returns `7`.
- `cooperative_green_spawn(worker)` builds and runs natively without the prior
  segfault.

Function-valued arrays and function-valued globals remain open storage/codegen
blockers and are not required for the current eager-result cooperative queue.

The cross-language harness now reports Simple OS-thread and Simple cooperative
green rows separately. A 20-worker OS-thread fanout smoke compiles and runs
through unrolled `thread_spawn` fork-join handles. `thread_spawn_with_args`
native probes now pass the focused explicit-argument ABI smoke, so it is no
longer part of this blocker list. The remaining direct-run blockers are the
cooperative green SMF mutable-global failure and native/SMF function-valued
array/global storage/codegen failures; those are runtime/compiler issues, not
public API change requests.

## Multicore Green SMF Status

The native `multicore_green_spawn` path has separate runtime-pool evidence:
`test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` exits nonzero if
any handle reports `used_runtime_pool() == false`. Current native evidence
passes that gate.

2026-06-08 update: native multicore-green rows execute with runtime-pool
evidence and checksum validation in the checked-in smoke reports. The SMF
runtime-pool wrapper lookup blocker is closed by
`test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl`,
which requires `wrapper_smf_pool_pass=true`; the historical blocker remains in
`doc/08_tracking/bug/smf_runtime_pool_closure_lookup_2026-06-07.md`.

Remaining SMF failures are cooperative-green queue rows, which still depend on
mutable global queue state and are not M:N CPU-parallel evidence. Keep those
classified separately from native and SMF `multicore_green_spawn` evidence.

## Reproduction

Temporary local repro files were created under `build/tmp/` while investigating:

- `global_array_append_smoke.spl`
- `global_usize_smoke.spl`

## Required Fix

Fix native and SMF handling for function-valued globals/arrays and mutable
global state, then switch or add a perf harness green row for delayed
`green_spawn(fn)` closure execution timing. Keep
`test/05_perf/profile_scripts/native_function_value_callback_regression_test.shs`
passing so the fixed function-parameter callback path does not regress.

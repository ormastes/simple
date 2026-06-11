# Green Thread Direct Runtime Blockers

Date: 2026-06-06

## Summary

Direct green-thread perf checks exposed runtime/compiler blockers that are
separate from the cooperative queue semantics:

- Direct/native function-parameter callbacks previously segfaulted for
  `fn call(cb: fn() -> i64) -> i64: cb()`. Fixed on 2026-06-08 by
  materializing top-level function values as closure objects before parameter
  passing.
- Direct `simple run` global function calls and global function-array
  append/index previously segfaulted after mutation. Fixed on 2026-06-08 by
  running JIT module init before entry calls and registering the init function
  for finalization lookup.
- SMF mutable globals previously segfaulted even for a minimal counter.
  Fixed on 2026-06-09 by preserving BSS sections in linked SMF output and
  resolving local data symbols against their loaded section base.
- SMF function-valued globals and global function-valued arrays previously
  segfaulted because the SMF execution path reached `spl_main` without first
  running `__module_init`. Fixed on 2026-06-11 by running the SMF module init
  function before entry calls.

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

Until SMF paths can safely store and call function-valued globals and global
array entries, `green_spawn(fn)` must keep the stable eager-result behavior for
broad profile rows. `green_spawn_value(result)` remains the stable profile
harness input for direct queue/fanout timing.

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

Local function-valued arrays, function-valued globals, and global
function-valued arrays are now native-covered by the callback regression script.
Function-valued globals and global function-valued arrays are also covered by
direct `simple run` checks in that script. SMF function-valued
global/global-array storage now has matching regression coverage.

2026-06-11 follow-up: the standalone native cooperative-green crashes are now
closed. The remaining compiled cooperative lane is no longer blocked on direct
`cooperative_green_spawn(worker)` or imported
`cooperative_green_spawn_value(...)` execution:

- the standalone native compile path now applies the same hybrid transform used
  by the SMF/native-memory path, so imported stdlib helpers keep the same
  fallback boundary instead of forcing direct AOT codegen;
- self-receiver field/method helper bodies now classify as compilable, which
  keeps `GreenThreadHandle.is_done()` and `GreenThreadHandle.join()` on the
  native path instead of falling back through the standalone native
  `rt_interp_call()` nil stub;
- the one-object standalone native main shim now calls `__module_init()` before
  `spl_main()`, which closes the mutable-global scheduler crash in
  `green_spawn_value()` even though the emitted ELF `.init_array` remained empty
  for this path.

Focused regression coverage still lives in:

- `test/03_system/feature/usage/cooperative_green_compiled_handle_array_blocker_spec.spl`
- `test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl`

The cross-language harness now reports Simple OS-thread and Simple cooperative
green rows separately. A 20-worker OS-thread fanout smoke compiles and runs
through unrolled `thread_spawn` fork-join handles. `thread_spawn_with_args`
native probes now pass the focused explicit-argument ABI smoke, so it is no
longer part of this blocker list.

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

SMF mutable-global regression evidence is now covered by
`test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl`.
SMF function-valued global/global-array regression evidence is now covered by
`test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl`,
which keeps both minimal SMF fixtures compiling and requires their pass markers
after the SMF `__module_init` execution fix.
Compiled cooperative-green handle-array blocker evidence is now covered by
`test/03_system/feature/usage/cooperative_green_compiled_handle_array_blocker_spec.spl`,
which now acts as regression coverage for interpreter, SMF, and standalone
native `cooperative_green_spawn(worker)` execution.
Imported cooperative helper fallback blocker evidence is now covered by
`test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl`,
which now acts as regression coverage for interpreter, SMF, and standalone
native `cooperative_green_spawn_value(...)` execution.
Cooperative-green queue rows are still not M:N CPU-parallel evidence; keep them
classified separately from native and SMF `multicore_green_spawn` evidence.

Separate from those runtime-path fixes, the SSpec runner still has an active
green/cooperative assertion mismatch:

- direct `simple run` probes pass
- equivalent `simple test` probes fail

That runner boundary is tracked separately in
`doc/08_tracking/bug/green_thread_spec_runner_mismatch_2026-06-11.md`.

## Reproduction

Temporary local repro files were created under `build/tmp/` while investigating:

- `global_array_append_smoke.spl`
- `global_usize_smoke.spl`

## Closed Repro

Verified again on 2026-06-11 with
`build/cargo-isolated/debug/simple compile ... -o fixture.smf` followed by
`build/cargo-isolated/debug/simple fixture.smf`:

- function-valued global slot SMF fixture -> prints
  `function_global_smf_pass=true`
- global function-valued array SMF fixture -> prints
  `global_function_array_smf_pass=true`

The focused regression spec above keeps that fixed path executable.

## Follow-Up

Switch or add a perf harness green row for delayed `green_spawn(fn)` closure
execution timing. Keep
`test/05_perf/profile_scripts/native_function_value_callback_regression_test.shs`
passing so the fixed callback, SMF import/classification path, standalone
native cooperative-green init path, and direct-run function-global paths do not
regress. The profile harness can now keep its compiled cooperative-green rows
on `cooperative_green_spawn`.

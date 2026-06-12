# Host Multicore Green Fairness and Preemption Gap

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The hosted `multicore_green_spawn` lane now has real runtime-pool evidence:

- `used_runtime_pool()` and `pool_used=N/N` are enforced in profile rows
- hosted reports require `queue_model=work_stealing`
- Go-vs-C-vs-Simple stress evidence is current

That is enough for bounded CPU-parallel M:N candidate claims, but it is still
not enough for full Go-like scheduler parity on the host runtime.

The remaining host-side gap is the same one called out in the selected
requirements, research, and architecture docs:

- fairness/preemption is not yet proven end to end for hosted multicore green

## Why This Is Still Open

Current hosted multicore-green evidence proves:

- runtime-pool ownership
- bounded parallelism
- work-stealing queue reporting
- fanout/fanin checksum integrity

Current hosted multicore-green evidence does not yet prove:

- long-running CPU work is preempted or yield-forced with a host-side contract
- host fairness semantics comparable to Go's scheduler under sustained loop load

Current best explicit host-fairness experiment now has executable native
regression coverage:

- `test/03_system/feature/usage/multicore_green_resumable_stepper_native_regression_spec.spl`
  writes a generated resumable-stepper probe that:
  - uses the existing hosted `multicore_green` worker pool
  - keeps work items scalar by queueing only callback ids and indexes
  - returns `result=7` with `EXIT=0` in the hosted native binary
- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
  is now the closed historical blocker record for that path
- `doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md`
  records the closed narrower native regression after joining a worker and doing
  extra post-join string work before returning a local result array. That
  regression now prints `result=7` with `EXIT=0`.
- `doc/08_tracking/bug/multicore_green_helper_handles_return_native_blocker_2026-06-11.md`
  records the closed helper handle-array return boundary. The corrected
  generated-source regression now type-checks real multi-line Simple source,
  compiles it to hosted native, and observes `after=7` with `EXIT=0`.

Current hosted blocking-compensation evidence now includes:

- `test/03_system/feature/usage/multicore_green_blocking_compensation_gap_spec.spl`
  keeps the hosted compensation-worker fix covered: with hosted pool
  parallelism pinned to `2`, two sleeping tasks still allow a third quick task
  to complete within the first 30ms window on both source-run and standalone
  native paths
- blocking compensation now has executable hosted coverage; the remaining host
  parity gap is fairness/preemption

Current hosted parallelism-boundary evidence also includes:

- `test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl`
  now regression-covers the bounded-parallelism fix: with requested hosted
  parallelism `2`, the fresh hosted runtime stays at `2` under CPU saturation
- bounded parallelism now has executable hosted regression coverage

Current hosted fairness-gap evidence also includes:

- `test/03_system/feature/usage/multicore_green_fairness_preemption_gap_spec.spl`
  keeps the one-worker monopolization boundary explicit: with hosted
  parallelism pinned to `1`, one tight CPU task can still keep a later quick
  task unfinished during the first short observation window
- `test/03_system/feature/usage/multicore_green_thread_yield_gap_spec.spl`
  proves raw `thread_yield()` is not enough for hosted fairness: even with
  `thread_yield()` inside the monopolizing task, the later quick task still
  does not finish during that same first short observation window
- `test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl`
  proves the explicit Pure Simple sliced-task API is the current positive
  hosted fairness path: with hosted parallelism pinned to `1`, a long
  `multicore_green_spawn_sliced` task requeues itself between short slices, a
  later quick `multicore_green_spawn` finishes during the first observation
  window, and the pool width still reports `parallelism_after_join=1`.

SimpleOS has scheduler-facing timer/runtime/compiler safepoint coverage for its
green-carrier lane, but that is not the same as proving the hosted runtime-pool
lane has equivalent fairness/preemption guarantees.

Related active host-side blocker:

- `doc/08_tracking/bug/multicore_green_sliced_native_closure_blocker_2026-06-11.md`
  is now a historical blocker record for the earlier captured-mutable-state
  prototype. The current public sliced API uses scalar state and a step
  function, and the regression spec above now proves source-run and native
  `EXIT=0`.
- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
  records the newer callback-id resumable-stepper prototype as closed. That
  path removes function-valued queue items and now returns `result=7` with
  `EXIT=0` in the debug-seed hosted native path.
- `doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md`
  records the closed post-join array-return continuation regression with
  `EXIT=0`.
- `doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md`
  now records the closed smaller hosted-native blocker that used to sit beneath
  that stepper path: a direct native array of a by-value struct is green again
  on current-source seed/native.
- `doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md`
  now records the closed smaller hosted-native blocker beneath that stepper
  path: local `MulticoreGreenHandle` array iteration plus `join()` now returns
  `result=7` with `EXIT=0`.
- `doc/08_tracking/bug/multicore_green_helper_handles_return_native_blocker_2026-06-11.md`
  now records the closed helper handle-array return boundary beneath that
  stepper path: a helper can keep local `MulticoreGreenHandle` handles, join
  them, and return a separate ordered result array with `EXIT=0`.
- `doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md`
  now records the closed standalone-native blocker that used to sit underneath
  that stepper path: returning a function value from inside a loop/search
  branch is green again even without the worker pool.
- `doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md`
  now records the closed helper-return regression that used to sit below the
  stepper path.
- `doc/08_tracking/bug/multicore_green_release_binary_stale_2026-06-11.md`
  records the newer evidence split: the checked-in `bin/release/simple` binary
  is stale for this lane, while current-source rebuilt `release` and `debug`
  artifacts are the stronger evidence for hosted-native regression checks.
  The native symbol-collision sub-bug (`worker.1`) is fixed there, and rebuilt
  helper-return and resumable-stepper probes now pass at runtime.

## Current Evidence Boundary

Current positive hosted evidence:

- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
- `test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl`
- `test/05_perf/stress/multicore_green_fanout_spec.spl`
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`

Current SimpleOS fairness/preemption evidence:

- `test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl`
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`

These do not yet close the hosted-runtime parity claim.

## Exit Criteria

This gap can close only when the hosted multicore-green lane has executable
evidence for:

- fairness/preemption for ordinary long-running closures, or a decision that
  the explicit sliced API is the supported hosted fairness contract and profile
  evidence/docs are updated to use it

That evidence must be tied into the canonical multicore-green feature tracking
and must not rely on SimpleOS-only scheduler proofs.

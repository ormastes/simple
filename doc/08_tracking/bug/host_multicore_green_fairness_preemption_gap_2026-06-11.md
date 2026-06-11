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

Current best explicit host-fairness experiment now also has executable blocker
coverage:

- `test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl`
  writes a generated resumable-stepper probe that:
  - uses the existing hosted `multicore_green` worker pool
  - keeps work items scalar by queueing only callback ids and indexes
  - still crashes in the hosted native binary before returning the first
    completion
- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
  is the narrowed blocker record for that path
- `test/03_system/feature/usage/native_function_value_param_array_regression_spec.spl`
  now records that the lower current-source native blocker beneath that path is
  closed: a function-valued local or parameter stored into an array is green
  again on current-source native
- `doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md`
  is the historical blocker record for that lower path and now marks it closed

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
- `test/03_system/feature/usage/multicore_green_fairness_preemption_gap_spec.spl`
  keeps the one-worker fairness gap explicit: with hosted parallelism pinned
  to `1`, a tight CPU loop can still keep a later quick task unfinished during
  the first short observation window
- `test/03_system/feature/usage/multicore_green_thread_yield_gap_spec.spl`
  keeps the deeper host-side point explicit: raw `thread_yield()` inside that
  one-worker task is still not enough to make queued work progress during the
  same early window

SimpleOS has scheduler-facing timer/runtime/compiler safepoint coverage for its
green-carrier lane, but that is not the same as proving the hosted runtime-pool
lane has equivalent fairness/preemption guarantees.

Related active host-side blocker:

- `doc/08_tracking/bug/multicore_green_sliced_native_closure_blocker_2026-06-11.md`
  records a reverted additive prototype for explicit resumable sliced tasks.
  That experiment narrowed the next host-runtime boundary again: the native
  captured-closure/state path for repeated pool-task requeue still ends in
  `exit=139`, so explicit sliced-task support is not ready to claim yet.
- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
  records the newer callback-id resumable-stepper prototype. That path removes
  function-valued queue items, but a single completed stepper still segfaults
  in the debug-seed hosted native path with `EXIT=139`.
- `doc/08_tracking/bug/multicore_green_worker_callback_registry_native_blocker_2026-06-11.md`
  now records the smaller hosted-native blocker beneath that stepper path: a
  pool worker that only looks up a callback id in the global registry and
  invokes that callback still crashes with `EXIT=139`.
- `doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md`
  now records the closed smaller hosted-native blocker that used to sit beneath
  that stepper path. A pool worker sending a plain struct payload through a
  channel is green again on current-source native, and the direct helper-side
  `Channel.id()` native path beneath it is green as well.
- `doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md`
  now records the closed standalone-native blocker that used to sit underneath
  that stepper path: returning a function value from inside a loop/search
  branch is green again even without the worker pool.
- `doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md`
  now records the closed helper-return regression that used to sit below the
  stepper path.
- `doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md`
  now records the lower param-array path as closed, so it is no longer the
  active blocker underneath the worker-pool stepper path.
- `doc/08_tracking/bug/multicore_green_worker_callback_registry_native_blocker_2026-06-11.md`
  now records the former worker callback-registry blocker as closed. The newer
  lower blocker is the helper handle-array return path in
  `doc/08_tracking/bug/multicore_green_helper_handles_return_native_blocker_2026-06-11.md`.
- `doc/08_tracking/bug/native_helper_print_return_blocker_2026-06-11.md`
  now records the smaller current-source native blocker beneath that hosted
  helper path as historical and closed: helper return values after built-in
  `println` no longer come back as `3`.
- `doc/08_tracking/bug/multicore_green_release_binary_stale_2026-06-11.md`
  records the newer evidence split: the checked-in `bin/release/simple` binary
  is stale for this lane, while current-source rebuilt `release` and `debug`
  artifacts are the stronger evidence for the remaining hosted-native blocker.
  The native symbol-collision sub-bug (`worker.1`) is fixed there, but the
  rebuilt helper-return and resumable-stepper probes still fail at runtime.

## Current Evidence Boundary

Current positive hosted evidence:

- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
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

- fairness/preemption or an equivalent enforced host-side yield contract

That evidence must be tied into the canonical multicore-green feature tracking
and must not rely on SimpleOS-only scheduler proofs.

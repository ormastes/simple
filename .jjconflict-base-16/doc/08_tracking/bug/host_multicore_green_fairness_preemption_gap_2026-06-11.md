# Host Multicore Green Fairness and Preemption Gap

Date: 2026-06-11
Status: closed; ordinary loop-body fairness now has compiler/runtime safepoint evidence
Owner: multicore-green lane

## Summary

The hosted `multicore_green_spawn` lane now has real runtime-pool evidence:

- `used_runtime_pool()` and `pool_used=N/N` are enforced in profile rows
- hosted reports require `queue_model=work_stealing`
- Go-vs-C-vs-Simple stress evidence is current

That is enough for bounded CPU-parallel M:N candidate claims. The hosted
fairness decision now has two executable paths: explicit scalar-state fairness
through `multicore_green_spawn_sliced`, and ordinary loop-body fairness through
compiler-inserted runtime-pool safepoints in `multicore_green_spawn` closures.

Plain `multicore_green_spawn` closures still run cooperatively at compiler
safepoint boundaries, not by arbitrary async stack preemption. The previous open
host-side gap is closed for tight loop bodies with source-run and standalone
native evidence.

## Why This Was Open

Current hosted multicore-green evidence proves:

- runtime-pool ownership
- bounded parallelism
- work-stealing queue reporting
- fanout/fanin checksum integrity

Historical hosted multicore-green evidence deliberately did not claim:

- ordinary long-running closures are preempted or yield-forced
- plain-closure fairness semantics comparable to Go's async preemption under
  sustained tight-loop load

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

Current hosted fairness/preemption evidence now includes:

- `test/03_system/feature/usage/multicore_green_fairness_preemption_gap_spec.spl`
  regression-covers ordinary loop-body fairness: with hosted parallelism
  starting at `1`, one tight CPU task now reaches compiler-inserted
  runtime-pool safepoints and a later quick task finishes during the first short
  observation window
- `test/03_system/feature/usage/multicore_green_thread_yield_gap_spec.spl`
  regression-covers the same compiler/runtime safepoint path when user code also
  calls raw `thread_yield()`, keeping fairness attributed to runtime-pool
  safepoints rather than bare OS-thread yielding
- `test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl`
  proves the explicit Pure Simple sliced-task API is the current positive
  hosted fairness path: with hosted parallelism pinned to `1`, a long
  `multicore_green_spawn_sliced` task requeues itself between short slices, a
  later quick `multicore_green_spawn` finishes during the first observation
  window, and the pool width still reports `parallelism_after_join=1`.
- `scripts/check/check-cross-language-perf.shs` now emits a separate
  `Hosted Fairness Evidence` section with `Simple sliced (source)` and
  `Simple sliced (native)` rows. The profile-report contract requires
  `multicore_green_spawn_sliced used_runtime_pool=true, quick_done=true, parallelism=1, total=9`, so
  this explicit sliced path remains visible separately from compiler-inserted
  ordinary loop-body safepoints.
- `test/05_perf/profile_scripts/concurrency_api_contract_test.shs` also keeps
  the public sliced API executable by requiring the run/join marker
  `public_multicore_green_sliced_result=19 used_runtime_pool=true`.

SimpleOS has scheduler-facing timer/runtime/compiler safepoint coverage for its
green-carrier lane, but that is not the same as proving the hosted runtime-pool
lane has equivalent fairness/preemption guarantees.

Related historical host-side blockers:

- `doc/08_tracking/bug/multicore_green_sliced_native_closure_blocker_2026-06-11.md`
  is now a historical blocker record for the earlier captured-mutable-state
  prototype. The current public sliced API uses scalar state and a step
  function, and the regression spec above now proves source-run and native
  `EXIT=0`.
- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
  now records the closed explicit scalar-state stepper path; it is no longer
  the remaining hosted parity gap.
- `doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md`
  now records the closed standalone-native blocker that used to sit underneath
  that stepper path: returning a function value from inside a loop/search
  branch is green again even without the worker pool.
- `doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md`
  now records the closed helper-return regression that used to sit below the
  stepper path.
- `doc/08_tracking/bug/multicore_green_release_binary_stale_2026-06-11.md`
  records the newer evidence split: the checked-in `bin/release/simple` wrapper
  is stale for this lane because its platform target is missing in this
  workspace, while current-source debug artifacts are the stronger evidence for
  hosted-native regression checks. The native symbol-collision sub-bug
  (`worker.1`) is fixed there, and debug-native helper-return and
  resumable-stepper probes now pass at runtime.

## Current Evidence Boundary

Current positive hosted evidence:

- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
- `test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl`
- `test/03_system/feature/usage/multicore_green_fairness_preemption_gap_spec.spl`
- `test/03_system/feature/usage/multicore_green_thread_yield_gap_spec.spl`
- `test/05_perf/stress/multicore_green_fanout_spec.spl`
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`

Current SimpleOS fairness/preemption evidence:

- `test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl`
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`

These close the supported hosted fairness contract for explicit sliced work and
ordinary loop-body closures. Non-loop long-running native calls remain outside
this compiler safepoint evidence.

## Closure Criteria

This tracker is closed for the supported hosted fairness contract because the
lane now has executable evidence for:

- the selected requirement naming `multicore_green_spawn_sliced` as the hosted
  CPU-heavy fairness contract
- source-run and native `multicore_green_spawn_sliced` fairness regression
  coverage
- profile `Hosted Fairness Evidence` rows
- public API and misuse coverage for the sliced API
- compiler-inserted runtime-pool safepoints in ordinary `while`, `loop`, and
  `for` loop bodies
- source-run and native ordinary loop-body fairness regression coverage

Future work must keep any broader claims separate: arbitrary long-running
native calls and straight-line CPU work without loop safepoints are not proven
by this tracker.

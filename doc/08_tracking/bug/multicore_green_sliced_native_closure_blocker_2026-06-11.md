# Multicore Green Sliced Native Closure Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

An early local additive prototype for explicit resumable host-side sliced tasks
was attempted in `src/lib/nogc_async_mut/concurrent/multicore_green.spl` and
then reverted because the hosted native path was not stable enough to ship.

The historical task-object shape that was tried:

- `MulticoreGreenSliceTask`
- `MulticoreGreenSliceResult`
- `multicore_green_spawn_sliced(...)`

That captured-mutable-state prototype failed on the native hosted path. The
current public API closes this blocker with a simpler scalar-state contract:
it does not expose `MulticoreGreenSliceTask` or `MulticoreGreenSliceResult`;
it exposes `MulticoreGreenSlicedHandle` and
`multicore_green_spawn_sliced(initial_state, step_fn)`.

## What Was Proven

- interpreter-mode sliced fallback could be made to complete the explicit
  step-by-step sum task correctly after removing recursive inline slice growth
- the remaining failure was narrower than "multicore green fairness is vague":
  it was specifically the hosted native closure/runtime boundary for resumable
  captured slice state
- the scalar-state public API now completes in source-run and hosted native
  while preserving the bounded pool width

## Historical Failure

Observed during direct hosted native verification:

- `SIMPLE_LIB=src bin/release/simple compile test/01_unit/lib/nogc_async_mut/multicore_green_native.spl --native`
  compiled successfully
- running the resulting binary ended with:
  `exit=139`

The failing experiment used a zero-arg closure field that captured a mutable
state object and advanced one explicit slice per pool task.

## Current Passing Evidence

- `test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl`
  checks the supported scalar-state API on source-run and standalone native.
- The fixture prints `quick_done_during_slices=true`,
  `parallelism_after_join=1`, `total=9`, and exits with `EXIT=0`.

## Why This Matters

This remains the shortest additive path currently identified toward host-side
resumable M:N work without claiming automatic preemption for plain
`fn() -> i64` tasks.

The blocker is now closed for the scalar-state API:

- plain OS-thread yield is not enough
- compiler safepoints are still a longer path
- explicit sliced tasks are supported when user code exposes scalar progress
  state through `multicore_green_spawn_sliced`

## Next Step

Continue investigating the broader hosted native runtime/codegen boundary for:

- zero-arg captured closures stored in task objects
- mutable captured state across repeated pool-task requeue
- closure field invocation under the runtime-pool worker path

Do not claim automatic preemption for plain `multicore_green_spawn` closures
until that separate host fairness/preemption path has executable evidence.

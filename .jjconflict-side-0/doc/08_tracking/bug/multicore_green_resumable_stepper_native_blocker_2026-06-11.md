# Multicore Green Resumable Stepper Native Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

Closed. The explicit host-fairness stepper path now type-checks, compiles to
hosted native, runs through a runtime-pool worker, returns `result=7`, and exits
with `EXIT=0`.

The stepper design is still intentionally explicit rather than automatic
preemption:

- step callbacks are registered globally by numeric id
- queue items carry only scalar ids and indexes
- one worker resumes one step at a time and requeues yielded work

The earlier helper-returned function-value blocker, struct-array blocker,
loop-return blocker, handle-array join blocker, inline lambda array-literal
blocker, pool/channel struct-send blocker, and post-join array-return blocker
below this path are closed.

## Minimal Boundary

Current minimal probe:

- one worker
- one registered stepper
- the stepper immediately returns `StepResult.completed(7)`
- the native run prints `result=7`
- the native run prints `EXIT=0`

So this is no longer a vague fairness gap and no longer an active native
stepper blocker. The scheduler path proves:

- rebuilt native hosted worker-pool execution accepts the stepper callback
- the channel result returns to the main thread
- the handle array joins the worker
- the ordered result array contains `7`

## Remaining Gap

The broader host-side Go-parity gap remains tracked in
`doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`.
That gap is about ordinary closure fairness/preemption semantics, not this
explicit scalar-state resumable stepper path.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl`
- `test/03_system/feature/usage/multicore_green_resumable_stepper_native_regression_spec.spl`

Both specs write the current probe source, type-check it under the fresh
compiler, compile it to native, and confirm `result=7` with `EXIT=0`.

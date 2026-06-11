# Multicore Green Resumable Stepper Native Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The best explicit host-fairness path found so far is a resumable stepper
scheduler layered over the existing hosted `multicore_green` worker pool:

- step callbacks are registered globally by numeric id
- queue items carry only scalar ids and indexes
- one worker resumes one step at a time and requeues yielded work

That design type-checks and compiles to a hosted native binary, but the hosted
native binary still segfaults before returning the first completion. The
earlier helper-returned function-value blocker that sat below this path is now
closed. The direct helper-side `Channel.id()` native fallback is also closed.
The former lower blocker beneath this path is tracked separately in
`doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md`
and is now closed.
The earlier lower pool-plus-struct-send blocker in
`doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md`
is already closed. Historical loop-return tracking remains in
`doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md`,
and that earlier loop-return blocker is also closed.

## Minimal Boundary

Current minimal probe:

- one worker
- one registered stepper
- the stepper immediately returns `StepResult.completed(7)`

Observed native output:

```text
Segmentation fault (core dumped)
EXIT=139
```

So this is no longer a vague “fairness is hard” gap. The narrower remaining
worker-pool blocker is:

- rebuilt native hosted worker-pool execution for the resumable-stepper probe crashes
- even when the work item is a single callback-id step with immediate completion
- that crash remains after the helper-returned function-value regression was
  fixed and moved out of the critical path
- the earlier loop/search helper-return path is now green
- the lower function-valued local or parameter array path is now closed beneath it

## Why This Matters

This experiment is the most credible pure-Simple route toward hosted fairness
without pretending plain `fn() -> i64` tasks are preemptible:

- keep the existing `multicore_green` bounded carrier pool
- make work explicitly resumable in user-space slices
- requeue yielded work fairly on the same pool

Until the native crash is fixed, that path cannot be promoted from experiment to
supported library surface.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl`

That spec writes the current probe source, type-checks it under the fresh
compiler, compiles it to native, and confirms the current `EXIT=139` boundary.

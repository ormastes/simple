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
earlier helper-returned function-value blocker that first narrowed this lane is
now closed; the remaining crash persists after that fix.

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

So this is no longer a vague “fairness is hard” gap. The current blocker is:

- rebuilt native hosted worker-pool execution for the resumable-stepper probe crashes
- even when the work item is a single callback-id step with immediate completion
- that crash still reproduces after the helper-returned function-value
  regression was fixed

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

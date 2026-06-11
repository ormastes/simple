# Multicore Green Resumable Stepper Native Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

The best explicit host-fairness path found so far is a resumable stepper
scheduler layered over the existing hosted `multicore_green` worker pool:

- step callbacks are registered globally by numeric id
- queue items carry only scalar ids and indexes
- one worker resumes one step at a time and requeues yielded work

<<<<<<< Conflict 1 of 2
+++++++ Contents of side #1
That design now type-checks, compiles to hosted native, runs through a
runtime-pool worker, returns `result=7`, and exits with `EXIT=0`. The earlier
helper-returned function-value blocker, struct-array blocker, loop-return
blocker, handle-array join blocker, and inline lambda array-literal blocker
below this path are closed.

The remaining crash found during reduction is narrower and no longer blocks the
resumable-stepper algorithm itself: post-join string work before returning a
local array from the same function still crashes in native. That lower issue is
tracked separately in
`doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md`.
%%%%%%% Changes from base to side #2
 That design type-checks and compiles to a hosted native binary, but the hosted
 native binary still segfaults before returning the first completion. The
 earlier helper-returned function-value blocker that sat below this path is now
 closed. The current lower blocker beneath this path is now tracked separately in
-`doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md`.
-That lower pool-plus-struct-send blocker sits below the worker-pool stepper
-path itself. Historical loop-return tracking remains in
+`doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md`.
+The older direct native struct-array blocker below that layer is now closed and
+kept as regression coverage in
+`doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md`.
+Historical loop-return tracking remains in
 `doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md`.
 That earlier loop-return blocker is also closed.
>>>>>>> Conflict 1 of 2 ends

## Minimal Boundary

Current minimal probe:

- one worker
- one registered stepper
- the stepper immediately returns `StepResult.completed(7)`

Observed native output for the scheduler path:

```text
result=7
EXIT=0
```

So this is no longer a vague “fairness is hard” gap and no longer an active
stepper blocker. The scheduler path proves:

<<<<<<< Conflict 2 of 2
+++++++ Contents of side #1
- rebuilt native hosted worker-pool execution accepts the stepper callback
- the channel result returns to the main thread
- the handle array joins the worker
- the ordered result array contains `7`
%%%%%%% Changes from base to side #2
 - rebuilt native hosted worker-pool execution for the resumable-stepper probe crashes
 - even when the work item is a single callback-id step with immediate completion
 - that crash remains after the helper-returned function-value regression was
   fixed and moved out of the critical path
 - the earlier loop/search helper-return path is now green
-- a smaller pool-worker struct-send path still crashes before the full stepper
-  machinery is required
+- a smaller hosted-native handle-array join path still fails before the full
+  stepper machinery is required
>>>>>>> Conflict 2 of 2 ends

## Why This Matters

This experiment is the most credible pure-Simple route toward hosted fairness
without pretending plain `fn() -> i64` tasks are preemptible:

- keep the existing `multicore_green` bounded carrier pool
- make work explicitly resumable in user-space slices
- requeue yielded work fairly on the same pool

This closes the algorithmic/native scheduler blocker. The narrower post-join
debug-output crash still needs compiler/runtime follow-up, but it is not the
M:N stepper path itself.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_resumable_stepper_native_regression_spec.spl`

That spec writes the current probe source, type-checks it under the fresh
compiler, compiles it to native, and confirms `result=7` with `EXIT=0`.

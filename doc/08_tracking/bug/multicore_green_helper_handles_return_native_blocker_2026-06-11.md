# Multicore Green Helper Handles Return Native Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The current lower hosted-native blocker beneath the resumable-stepper lane is
no longer worker callback lookup or worker-side channel send/recv.

Those lower paths now pass on current-source native. The active smaller crash
boundary is a helper that:

- keeps a local `handles` array of `MulticoreGreenHandle`
- appends one spawned worker handle into that array
- receives one completion successfully
- joins the stored handles in a `for handle in handles` loop
- returns a separate `ordered` result array to the caller

That helper still crashes on current-source native with `EXIT=139`.

The smaller generic helper post-`println` seed blocker that briefly sat beneath
this path is now closed in
`doc/08_tracking/bug/native_helper_print_return_blocker_2026-06-11.md`.

## Current Minimal Probe

```simple
fn run_one(stepper: Stepper) -> [i64]:
    val work = channel_new()
    val results = channel_new()
    work.send(StepTask(stop: false, index: 0, callback_id: stepper.callback_id))
    var handles = []
    handles.append(multicore_green_spawn(\: worker_loop(work.id(), results.id())))
    var ordered = [0]
    val completion = results.recv() as StepCompletion
    ordered[completion.index] = completion.value
    work.send(stop_task())
    for handle in handles:
        handle.join()
    ordered
```

Observed native output:

```text
before
EXIT=139
```

## What Is Already Closed Below This

These neighboring lower boundaries are now green on current-source native:

- direct callback-registry worker invoke
- one-shot worker receive plus completion send
- callback-id requeue send-back without the helper handle-array return path
- inline coordinator logic in `main`
- helper return without local handle-array iteration

So the remaining lower bug is more specific than “multicore_green workers
crash” or “channels crash”.

## Relationship To Other Blockers

- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`
- `doc/08_tracking/bug/multicore_green_worker_callback_registry_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/native_helper_print_return_blocker_2026-06-11.md`

The older worker-callback registry blocker is now closed. The higher
resumable-stepper blocker remains open above this narrower helper
handle-array-plus-return boundary. The temporary lower helper-print-return
blocker is also now closed beneath it.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_helper_handles_return_native_blocker_spec.spl`

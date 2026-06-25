# Multicore Green Helper Handles Return Native Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

The former lower hosted-native blocker beneath the resumable-stepper lane is
now closed on current-source native.

Those lower paths now pass on current-source native. The formerly active
smaller crash boundary was a helper that:

- keeps a local `handles` array of `MulticoreGreenHandle`
- appends one spawned worker handle into that array
- receives one completion successfully
- joins the stored handles in a `for handle in handles` loop
- returns a separate `ordered` result array to the caller

That helper now exits cleanly on current-source native with `EXIT=0` and prints
`after=7`.

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

Historical native output:

```text
before
EXIT=139
```

Current native output:

```text
before
after=7
EXIT=0
```

## What Is Already Closed Below This

These neighboring lower boundaries are now green on current-source native:

- direct callback-registry worker invoke
- one-shot worker receive plus completion send
- callback-id requeue send-back without the helper handle-array return path
- inline coordinator logic in `main`
- helper return without local handle-array iteration

So this lower bug is no longer active evidence against the resumable
multicore-green path. The broader hosted fairness/preemption gap remains open
in `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`.

## Relationship To Other Blockers

- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`
- `doc/08_tracking/bug/multicore_green_worker_callback_registry_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/native_helper_print_return_blocker_2026-06-11.md`

The older worker-callback registry blocker is now closed. This narrower helper
handle-array-plus-return boundary is also closed. The broader hosted
fairness/preemption gap remains open until the runtime has executable
fairness/preemption evidence comparable to Go under sustained loop load.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_helper_handles_return_native_blocker_spec.spl`

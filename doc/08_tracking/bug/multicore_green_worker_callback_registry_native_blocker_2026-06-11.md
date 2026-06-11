# Multicore Green Worker Callback Registry Native Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

This was the hosted-native blocker beneath the resumable-stepper lane before
the array-concat lowering fix landed in current source.

A `multicore_green` worker that only:

- receives a scalar callback id as a closure capture
- looks that id up in the global callback registry
- invokes the returned callback
- joins and returns the completed value

used to crash on current-source native.

Current minimal probe:

```simple
fn worker(callback_id: i64) -> i64:
    val step = get_stepper(callback_id)()
    if step.done:
        return step.value
    0

fn main() -> i64:
    multicore_green_set_parallelism(1)
    val callback_id = register_stepper(\: StepResult.completed(7))
    println("before")
    val handle = multicore_green_spawn(\: worker(callback_id))
    val value = handle.join()
    println("after=" + value.to_string())
    if value != 7:
        return 21
    0
```

Historical native output:

```text
before
EXIT=139
```

## Why This Matters

This proved the hosted-native fairness lane did not need channel traffic or
resumable queue re-enqueue to reproduce the crash. The lower bad edge was:

- callback-id registry lookup
- function-valued callback retrieval
- callback invocation inside the worker closure

That made this a better lower blocker than the older full resumable-stepper
note while this bug was still active.

## Relationship To Other Blockers

- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`
- `doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md`

The callback-registry worker boundary is now closed. The larger
resumable-stepper native blocker remains open above a different lower
boundary:

- `doc/08_tracking/bug/multicore_green_helper_handles_return_native_blocker_2026-06-11.md`

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_worker_callback_registry_native_blocker_spec.spl`

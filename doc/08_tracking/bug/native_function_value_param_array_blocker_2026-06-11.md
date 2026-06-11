# Native Function Value Param Array Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The current lower hosted-native blocker beneath the `multicore_green`
resumable-stepper lane is narrower than the older broad array-literal note.

A named function in an array literal is already green on current-source native.
But a function-valued parameter or local stored into an array still degrades on
native before the later indirect call.

Current minimal probe:

```simple
fn run_one(step_fn: fn() -> i64) -> i64:
    val callbacks = [step_fn]
    callbacks[0]()

fn main() -> i64:
    println("before")
    val v = run_one(\: 7)
    println("after=" + v.to_string())
    if v != 7:
        return 2
    0
```

Observed native output:

```text
before
after=3
EXIT=2
```

The same probe passes in source-run and compiles successfully to native before
the runtime degradation.

## Why This Matters

The active resumable-stepper experiment depends on storing callback-like
function values that are not only plain named globals:

- callback ids route into helper lookups
- helper-returned or local function values still pass through array storage
- the current native degradation appears before the higher worker-pool fairness
  lane, so that higher lane cannot be closed honestly yet

This is therefore a better lower blocker than the older broad array-literal
note for the current hosted fairness work.

## Relationship To Other Blockers

- `doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md`
- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`

The older array-literal blocker remains historically true for inline lambda
array literals that still crash with `EXIT=139`, but it is no longer the best
single lower bound for the current stepper lane.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_param_array_blocker_spec.spl`

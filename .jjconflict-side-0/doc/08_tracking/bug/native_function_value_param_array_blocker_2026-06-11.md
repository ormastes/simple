# Native Function Value Param Array Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

The former lower hosted-native blocker beneath the `multicore_green`
resumable-stepper lane was narrower than the older broad array-literal note.

A named function in an array literal is green on current-source native, and the
same is now true for a function-valued parameter or local stored into an array.

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

Current native output:

```text
before
after=7
EXIT=0
```

The same probe passes in source-run and now also passes in standalone native.

## Why This Matters

The active resumable-stepper experiment depends on storing callback-like
function values that are not only plain named globals:

- callback ids route into helper lookups
- helper-returned or local function values still pass through array storage
- this lower path is now closed, so the remaining higher worker-pool fairness
  lane can be discussed without this older false failure underneath it

This was therefore a better lower blocker than the older broad array-literal
note for the hosted fairness work, and it is now closed as regression-covered.

## Relationship To Other Blockers

- `doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md`
- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`

The older array-literal blocker remains a historical neighbor note, but this
param-array blocker is now closed and no longer an active lower bound.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_param_array_regression_spec.spl`

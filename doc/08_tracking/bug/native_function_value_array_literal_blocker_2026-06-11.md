# Native Function Value Array Literal Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The remaining hosted-native `multicore_green` resumable-stepper crash is not
the first bad boundary anymore. A smaller native bug already reproduces with a
plain array literal containing function values.

Current minimal native probe:

```simple
fn main() -> i64:
    println("before")
    val callbacks = [\: 7]
    val value = callbacks[0]()
    println("value=" + value.to_string())
    if value != 7:
        return 2
    0
```

Observed native output:

```text
before
EXIT=139
```

The same shape also reproduces with named function values in array literals.
By contrast, the lower `append` path is currently green:

- `var callbacks: [fn() -> i64] = []`
- `callbacks.append(\: 7)`
- `callbacks[0]()` -> returns `7`

So the current lower blocker is not generic function-value dispatch anymore. It
is the native path for array literals whose elements are function values.

## Why This Matters

The active resumable-stepper experiment depends on exactly this shape:

- `CALLBACKS = CALLBACKS + [step_fn]`

That expression creates a one-element array literal containing a function
value, then feeds it into array concatenation. Until function-value array
literals are correct on hosted native, the higher worker-pool stepper lane
cannot be closed honestly.

## Relationship To Higher Blockers

- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`

Those higher trackers remain open, but this file is now the lower native
boundary beneath them.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_array_literal_blocker_spec.spl`

# Native Function Value Array Literal Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

This tracker still captures a real lower native bug, but it is no longer the
best single lower bound for the hosted `multicore_green` resumable-stepper
lane. The current narrower active blocker for that lane is tracked separately
in `doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md`.

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

The same inline-lambda shape still reproduces today. By contrast, a named
function array literal is current-source native green, and the lower `append`
path is also green:

- `var callbacks: [fn() -> i64] = []`
- `callbacks.append(\: 7)`
- `callbacks[0]()` -> returns `7`

So this tracker now means something narrower:

- inline lambda array literals containing function values still crash on native
- it is not a generic named-function array-literal failure anymore
- it is not the best single lower bound for the current hosted fairness lane

## Why This Matters

The active resumable-stepper experiment depends on exactly this shape:

- `CALLBACKS = CALLBACKS + [step_fn]`

That expression creates a one-element array literal containing a function
value, then feeds it into array concatenation. But the more accurate current
lower bound for the stepper lane is the function-valued local or parameter
array path tracked separately in
`doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md`.

## Relationship To Higher Blockers

- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`

Those higher trackers remain open, but this file is now a neighboring lower
native boundary rather than the best single blocker under them.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_array_literal_blocker_spec.spl`

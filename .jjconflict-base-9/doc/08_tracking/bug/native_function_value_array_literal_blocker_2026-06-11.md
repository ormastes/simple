# Native Function Value Array Literal Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

This tracker captured a lower native bug beneath the hosted `multicore_green`
resumable-stepper lane. It is now closed: inline lambda array literals preserve
a function element type in HIR, stay unboxed in MIR array storage, and call
through the indexed closure with the lambda body return type.

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
value=7
EXIT=0
```

The same inline-lambda shape is now current-source native green. Named
function array literals and the lower `append` path remain green:

- `var callbacks: [fn() -> i64] = []`
- `callbacks.append(\: 7)`
- `callbacks[0]()` -> returns `7`

This closed tracker now records that:

- inline lambda array literals containing function values no longer crash on native
- the native probe prints `value=7`
- the native probe exits with `EXIT=0`

## Why This Matters

The active resumable-stepper experiment includes this shape:

- `CALLBACKS = CALLBACKS + [step_fn]`

That expression creates a one-element array literal containing a function
value, then feeds it into array concatenation. This lower piece is fixed, but
the higher resumable-stepper native blocker remains tracked separately.

## Relationship To Higher Blockers

- `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`
- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`

Those higher trackers remain open, but this lower native boundary is closed.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_array_literal_regression_spec.spl`

# Multicore Green Callable Field Runtime Blocker

Date: 2026-06-11
Status: fixed
Owner: multicore-green lane

## Summary

The remaining hosted multicore-green fairness experiment exposed a smaller and
more actionable runtime boundary than the broader sliced-task idea:
function-valued object fields backed by captured mutable state were previously
correct in source-run but not in standalone native. That boundary is now fixed.

This is relevant to any additive resumable/sliced-task direction because that
shape naturally wants task objects that hold a zero-argument closure field and
advance mutable state across repeated invocations.

## Reproduced Shape

Minimal hosted probe:

```simple
class Counter:
    value: i64

class ThunkHolder:
    thunk: fn() -> i64

fn make_holder(seed: i64) -> ThunkHolder:
    var counter = Counter(value: seed)
    val thunk = \:
        counter.value = counter.value + 1
        counter.value
    ThunkHolder(thunk: thunk)
```

Expected behavior:

- first `holder.thunk()` returns `41`
- second `holder.thunk()` returns `42`

## Fixed Behavior

Hosted source-run with `bin/release/simple run` now prints the expected
captured-thunk values:

```text
a=41
b=42
```

Fresh standalone native compile now runs the same escaped captured-closure
shape successfully:

```text
a=41
b=42
EXIT=0
```

## Why This Matters

The broader host fairness/preemption gap is still real, but this former blocker
is now closed:

- not just scheduler fairness prose
- not just raw `thread_yield()` insufficiency
- escaped captured closure values now survive source-run and standalone native

Until this is closed, additive sliced/resumable task objects are not stable
enough to claim on the hosted native path.

## Next Step

What fixed it:

- HIR callable-field result typing now uses the function return type instead of
  the function object type
- compilability analysis no longer forces needless hybrid `rt_interp_call`
  fallback for typed struct field access, struct init, and closure creation
- fresh native compiler/runtime now runs the same probe successfully

The executable regression coverage now lives in:

- `test/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.spl`

This note remains as the historical bug record for the closed boundary.

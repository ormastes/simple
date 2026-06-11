# Native Struct Array Runtime Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The remaining hosted-native `multicore_green` blocker is lower than the worker
pool and lower than callback-id stepper logic. A direct native array of a
by-value struct already misbehaves on current-source seed/native:

- source-run is correct
- native compile succeeds
- native run prints `result=3`
- native exit is `77`

So the live seed/runtime bug is now pinned as native struct-array element
storage or retrieval for by-value structs.

The stale helper-side hybrid fallback that used to sit above this boundary is
now closed: helper bodies that construct array literals are allowed to stay on
the native path again. The remaining failure is the lower native runtime
behavior for by-value struct arrays themselves, not a blanket helper
classification problem.

## Minimal Boundary

Current reduced probe:

```simple
class Boxed:
    value: i64
    fn get() -> i64:
        self.value

fn run_one() -> i64:
    val items = [Boxed(value: 7)]
    items[0].get()
```

Observed native output:

```text
result=3
EXIT=77
```

The direct non-array shape is green:

```simple
val boxed = Boxed(value: 7)
boxed.get() == 7
```

So the active lower boundary is not generic struct init or method dispatch by
itself. It is native array runtime behavior for by-value struct elements.

## Why This Matters

This sits underneath the remaining resumable-stepper host-fairness lane because
that experiment still relies on local arrays of Simple values such as handles
and ordered result buffers. Until native struct-array behavior is correct,
higher worker-pool fairness experiments can keep failing for the wrong reason.

## Executable Evidence

- `test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl`

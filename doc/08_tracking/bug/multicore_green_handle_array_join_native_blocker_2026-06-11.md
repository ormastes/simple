# Multicore Green Handle Array Join Native Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The smaller direct struct-array blocker beneath hosted `multicore_green` is now
closed. The active lower current-source seed/native blocker is one layer above
that boundary:

- a helper keeps a local `MulticoreGreenHandle` array
- it appends one spawned handle
- it iterates that array
- it calls `handle.join()`
- native compile succeeds
- native run prints `result={result}`
- native exit is `12`

So the live seed/runtime bug is now pinned as hosted-native handle-array
iteration or `join()` dispatch, not generic by-value struct-array storage.

## Minimal Boundary

Current reduced probe:

```simple
use std.concurrent.multicore_green.{multicore_green_spawn, multicore_green_set_parallelism}

fn run_one() -> i64:
    var handles = []
    handles.append(multicore_green_spawn(\: 7))
    var total = 0
    for handle in handles:
        total = total + handle.join()
    total

fn main() -> i64:
    multicore_green_set_parallelism(1)
    val result = run_one()
    println("result={result}")
    if result != 7:
        return 12
    0
```

Observed native output:

```text
result={result}
EXIT=12
```

The smaller direct struct-array path is now green:

```simple
val items = [Boxed(value: 7)]
items[0].get() == 7
```

So the active lower boundary is no longer generic array storage. It is
hosted-native handle-array iteration and `join()` behavior.

## Why This Matters

This sits directly underneath the remaining resumable-stepper host-fairness
lane because that experiment still relies on local arrays of worker handles and
ordered result buffers. Until local handle-array join is correct, the higher
stepper path can still fail for the wrong reason.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl`

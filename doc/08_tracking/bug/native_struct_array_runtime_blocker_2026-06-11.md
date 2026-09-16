# Native Struct Array Runtime Blocker

## Closed 2026-09-13 — already closed in-entry; behaviour re-checked on the current seed

- **inferred** The entry `Status: closed` is backed by an in-file record of what changed
  (narrowed compilability fallback / preserved native lowering), not a bare status flip.
- **measured** On the Rust seed v1.0.0-rc.1 (Windows) the shapes this blocker covers now
  execute correctly: a function-value array literal `[add1, add2]` walked by `for f in fns`
  and called per element prints `total=23`; helper returns and `me fn` methods mutating an
  array field accumulate correctly (`mefn=2`).
- **inferred** Standalone-native re-confirmation is not possible here: `bin/simple
  native-build` aborts with `SCV-E-SNAPSHOT: snapshot-cache-root-not-owned` and
  `unknown extern function: rt_env_vars` before codegen, for reasons unrelated to this bug.


Date: 2026-06-11
Status: closed 2026-09-13 (was: Status: closed)
Owner: multicore-green lane

## Summary

The former lower hosted-native `multicore_green` blocker beneath the worker
pool and callback-id stepper logic is now closed. A direct native array of a
by-value struct is green again on current-source seed/native:

- source-run is correct
- native compile succeeds
- native run prints `result=7`
- native exit is `0`

So the live seed/runtime bug is no longer native struct-array element storage
or retrieval for by-value structs.

The stale helper-side hybrid fallback above this boundary is also closed:
helper bodies that construct array literals stay on the native path again.
The active remaining lower blocker is now above this layer, in hosted
`MulticoreGreenHandle` array iteration and join.

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

Current native output:

```text
result=7
EXIT=0
```

The direct non-array shape is green:

```simple
val boxed = Boxed(value: 7)
boxed.get() == 7
```

So the active lower boundary is no longer generic array runtime behavior for
by-value struct elements.

## Why This Matters

This regression used to sit underneath the remaining resumable-stepper
host-fairness lane because that experiment relies on local arrays of Simple
values such as handles and ordered result buffers. With this layer green again,
the next remaining failure is the hosted handle-array join path itself.

## Executable Evidence

- `test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl`
- `doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md`

# Multicore Green Post-Join Array Return Native Blocker

Date: 2026-06-12
Status: closed
Owner: multicore-green lane

## Summary

The resumable-stepper scheduler itself is now native green, and the narrower
post-join continuation shape is fixed:

- run a `multicore_green` worker through a channel-backed stepper
- receive and store the completed value in a local result array
- send a stop task and join the worker
- perform extra string or print work after the join
- return the local result array

That standalone native binary now returns `result=7` with `EXIT=0`.

## Minimal Boundary

Current minimal probe shape:

```simple
fn run_steppers(steppers: [Stepper]) -> [i64]:
    ...
    handle.join()
    println("after_join=1")
    ordered
```

Historical native output:

```text
Segmentation fault (core dumped)
EXIT=139
```

Fixed native output:

```text
after_join=1
result=7
EXIT=0
```

Reduction evidence from 2026-06-12:

- `multicore_green` worker plus channel payload, no callback registry: green
- callback registry plus worker, no channel: green
- callback registry plus channel worker, direct handle: green
- `run_steppers([Stepper])` plus ordered result array, no post-join print:
  green
- adding post-join string work before returning the local result array used to
  produce `EXIT=139`; it now returns `EXIT=0`

Root cause fixed on 2026-06-12:

- the Rust seed compiler's hybrid compilability analysis treated any effect
  annotation or inferred effect as interpreter-only
- a Pure Simple function containing native-lowered `println` was compiled, but
  its callers were rewritten to `InterpCall`
- standalone native artifacts could not resolve that interpreter fallback and
  returned nil, which crashed at the array index use site
- effect annotations now remain metadata for capability/verification checks;
  only concrete unsupported constructs force interpreter fallback

## Why This Matters

This was a compiler/runtime native continuation bug, not the scheduler
algorithm itself. It remains covered because diagnostic or bookkeeping work
after joining a runtime-pool worker must be safe in normal Pure Simple code.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl`

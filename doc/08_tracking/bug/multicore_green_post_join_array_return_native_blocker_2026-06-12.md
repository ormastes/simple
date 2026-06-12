# Multicore Green Post-Join Array Return Native Blocker

Date: 2026-06-12
Status: open
Owner: multicore-green lane

## Summary

The resumable-stepper scheduler itself is now native green, but a narrower
post-join continuation shape still crashes:

- run a `multicore_green` worker through a channel-backed stepper
- receive and store the completed value in a local result array
- send a stop task and join the worker
- perform extra string or print work after the join
- return the local result array

That standalone native binary still segfaults with `EXIT=139`.

## Minimal Boundary

Current minimal probe shape:

```simple
fn run_steppers(steppers: [Stepper]) -> [i64]:
    ...
    handle.join()
    println("after_join=1")
    ordered
```

Observed native output:

```text
Segmentation fault (core dumped)
EXIT=139
```

Reduction evidence from 2026-06-12:

- `multicore_green` worker plus channel payload, no callback registry: green
- callback registry plus worker, no channel: green
- callback registry plus channel worker, direct handle: green
- `run_steppers([Stepper])` plus ordered result array, no post-join print:
  green
- adding post-join string work before returning the local result array:
  `EXIT=139`

## Why This Matters

This is a compiler/runtime native continuation bug, not the scheduler algorithm
itself. It still matters because diagnostic or bookkeeping work after joining a
runtime-pool worker should be safe in normal Pure Simple code.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl`

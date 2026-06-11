<<<<<<< Conflict 1 of 1
+++++++ Contents of side #1
# Multicore Green Channel Struct Send Native Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

The earlier lower native blocker beneath the hosted `multicore_green`
resumable-stepper fairness experiment was smaller than callback-id steppers:

- the direct main-thread `channel_new() -> send(7) -> recv() -> == 7` path is
  green in current-source debug/native evidence
- the direct helper `Channel(_id: id).id()` path is also green again in
  current-source native evidence
- a `multicore_green` worker sends a plain struct payload through a channel
- the main thread receives the payload and reaches the print path
- the standalone native binary now exits cleanly with the expected value

That means this lower boundary is no longer the active native blocker. Plain
channel roundtrip equality, helper-side `Channel.id()` dispatch, and the
smaller pool-worker struct-send path are all green again on current-source
native. The active hosted native blocker is back on the resumable-stepper lane.

## Minimal Boundary

Current reduced probe:

- `multicore_green_set_parallelism(1)`
- `channel_new()` on the main thread
- one pool worker:
  - `channel_from_id(result_id)`
  - `send(StepCompletion(index: 0, value: 7))`
  - `return 0`
- main thread:
  - `recv() as StepCompletion`
  - `h.join()`
  - `println("value={completion.value}")`

Current verified behavior:

```text
direct main-thread channel int equality: source-run passes
direct main-thread channel int equality: native run EXIT=0
direct helper Channel.id(): source-run passes
direct helper Channel.id(): native run EXIT=0
type-check: passes
native compile: passes
native run: prints value=7
native run: EXIT=0
```

## Why This Matters

The hosted fairness lane no longer needs to blame this smaller pool-plus-struct
path for the remaining native crash.

The callback-id resumable-stepper experiment remains blocked, but that blocker
is now higher and narrower than this path:

- the lower hosted-native pool/channel payload transport path is fixed
- the remaining host-side Go-like M:N gap stays on the resumable-stepper
  native crash path

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_channel_struct_send_native_regression_spec.spl`
%%%%%%% Changes from base to side #2
-# Multicore Green Channel Struct Send Native Blocker
-
-Date: 2026-06-11
-Status: open
-Owner: multicore-green lane
-
-## Summary
-
-The current lower native blocker beneath the hosted `multicore_green`
-resumable-stepper fairness experiment is smaller than callback-id steppers:
-
-- a `multicore_green` worker sends a plain struct payload through a channel
-- the main thread receives the payload and reaches the print path
-- the standalone native binary still ends with `EXIT=139`
-
-That means the remaining active crash is already present without callback
-lookup, stepper arrays, requeue logic, or `StepResult` indirect calls.
-
-## Minimal Boundary
-
-Current reduced probe:
-
-- `multicore_green_set_parallelism(1)`
-- `channel_new()` on the main thread
-- one pool worker:
-  - `channel_from_id(result_id)`
-  - `send(StepCompletion(index: 0, value: 7))`
-  - `return 0`
-- main thread:
-  - `recv() as StepCompletion`
-  - `h.join()`
-  - `println("value={completion.value}")`
-
-Observed behavior:
-
-```text
-type-check: passes
-native compile: passes
-native run: prints value={completion.value}
-native run: EXIT=139
-```
-
-## Why This Matters
-
-The hosted fairness lane should not blame resumable steppers first when a
-smaller pool-plus-struct-channel path is already crashing in current-source
-native artifacts.
-
-Until this lower bug is fixed:
-
-- the callback-id resumable-stepper experiment remains partially blocked by a
-  more basic hosted-native pool/channel payload path
-- the remaining host-side Go-like M:N gap is still entangled with native pool
-  result transport correctness
-
-## Executable Evidence
-
-- `test/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.spl`
>>>>>>> Conflict 1 of 1 ends

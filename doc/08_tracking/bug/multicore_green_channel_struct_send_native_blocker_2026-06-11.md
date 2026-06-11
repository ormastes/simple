# Multicore Green Channel Struct Send Native Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The current lower native blocker beneath the hosted `multicore_green`
resumable-stepper fairness experiment is smaller than callback-id steppers:

- a `multicore_green` worker sends a plain struct payload through a channel
- the main thread receives the payload and reaches the print path
- the standalone native binary still ends with `EXIT=139`

That means the remaining active crash is already present without callback
lookup, stepper arrays, requeue logic, or `StepResult` indirect calls.

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

Observed behavior:

```text
type-check: passes
native compile: passes
native run: prints value={completion.value}
native run: EXIT=139
```

## Why This Matters

The hosted fairness lane should not blame resumable steppers first when a
smaller pool-plus-struct-channel path is already crashing in current-source
native artifacts.

Until this lower bug is fixed:

- the callback-id resumable-stepper experiment remains partially blocked by a
  more basic hosted-native pool/channel payload path
- the remaining host-side Go-like M:N gap is still entangled with native pool
  result transport correctness

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.spl`

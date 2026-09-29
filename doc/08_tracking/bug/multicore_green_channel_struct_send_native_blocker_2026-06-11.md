# Multicore Green Channel Struct Send Native Blocker

## Closed 2026-09-13 — already closed in-entry; native boundary recorded as crossed

- **inferred** The entry's own `Status: closed` line is backed by an in-file "Fixed
  Behavior" / "now closed" section naming what changed, not a bare status flip.
- **measured** The general hosted-native closure family this blocker belongs to behaves
  correctly on the current Rust seed (v1.0.0-rc.1, Windows): a function-value array walked
  by `for f in fns` and called per element prints `total=23`, and `me fn` methods mutating
  an array field accumulate correctly (`mefn=2`).
- **inferred** Standalone-native re-confirmation is not possible on this host: `native-build`
  aborts with `SCV-E-SNAPSHOT: snapshot-cache-root-not-owned` / `unknown extern function:
  rt_env_vars` before codegen, for reasons unrelated to this bug.


Date: 2026-06-11
Status: closed 2026-09-13 (was: Status: closed)
Owner: multicore-green lane

## Summary

Closed. The lower native boundary beneath the hosted `multicore_green`
resumable-stepper fairness experiment is green:

- the direct main-thread `channel_new() -> send(7) -> recv() -> == 7` path is
  green in current-source debug/native evidence
- the direct helper `Channel(_id: id).id()` path is green in current-source
  native evidence
- a `multicore_green` worker sends a plain struct payload through a channel
- the main thread receives the payload and reaches the print path
- the standalone native binary prints `value=7`
- the standalone native binary exits with `EXIT=0`

That means this lower boundary is no longer the active native blocker. Plain
channel roundtrip equality, helper-side `Channel.id()` dispatch, and the
smaller pool-worker struct-send path are all green again on current-source
native.

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
type-check: passes
native compile: passes
native run: prints value=7
native run: EXIT=0
```

## Why This Matters

The hosted fairness lane no longer needs to blame this smaller pool-plus-struct
path for any remaining host-side Go-parity gap. Remaining hosted parity work is
tracked in:

- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.spl`
- `test/03_system/feature/usage/multicore_green_channel_struct_send_native_regression_spec.spl`

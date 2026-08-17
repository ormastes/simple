# CUDA lane reads the SVM-G budget sentinel as a device timeout, making budget expiry unobservable to a debugger

- **Date:** 2026-08-09
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Component:** `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl`
- **Found by:** P6 (DBG-1/PROF-1 CUDA wrapper), running the D3 debug
  conformance vector `budget_expiry_while_debugging` on a live device.

## Symptom

Of the 10 D3 debug conformance vectors, 9 diff clean device-vs-ref on every
field. `budget_expiry_while_debugging` cannot be checked at all:

```
V budget_expiry_while_debugging L0 ok=false err=[cuda-lane-device-timeout-sentinel] sc=0/5 sent=0/3735879680
V budget_expiry_while_debugging SHUTDOWN=[cuda-lane-session-cleanup-pending]
```

Expected sentinel `3735879680` = `0xDEAD0000` = `SENTINEL_TIMEOUT`, and
expected accumulated `DBG_STEP_COUNT` = 5. Both are reported as 0 because the
arena is never read back.

## Root cause

`SENTINEL_TIMEOUT` (`0xDEAD0000`) is the **VM-level budget-exhaustion**
sentinel. The kernel writes it correctly — this is a normal, expected SVM-G
outcome, not a fault. But `CudaLaneSession.launch_once` decodes that same
sentinel as a **device** timeout:

```
if decode_sentinel(sentinel_raw) == SentinelState.Timeout:
    self.completion_unknown = true
    self.release_pending = true
    return self._fail("cuda-lane-device-timeout-sentinel")
```

Two consequences, both fatal to observing the vector:

1. `launch_once` returns an error, so `run_source_persisting_data` returns
   `ok: false` with an empty `out_arena` — the saved DBG-1 block is never
   read, so `saved_pc` / `step_count` / stack are unobservable.
2. `completion_unknown` / `release_pending` latch, so `shutdown()` returns
   `cuda-lane-session-cleanup-pending` and the session cannot be cleanly
   retired.

The latch itself is **deliberate** and must not be "fixed" — after a genuine
device timeout the completion state really is unknown. The defect is the
**conflation**: a VM that cleanly ran out of its instruction budget and
halted is not a device that stopped responding, yet both produce the same
arena word and the lane layer cannot tell them apart.

## Why the existing suite did not catch it

`cuda_vm_executor_conformance_spec.spl` explicitly `continue`s past its own
`_BUDGET_EXHAUSTION_TIMEOUT_VECTOR`, so the D3 conformance lane has never
exercised this path either. The skip predates DBG-1.

## Impact

A debugger on the CUDA lane can never report "your program exhausted its
step budget" — the one stop reason a step-budget-limited debugger most needs.
`DebugTarget`'s `STOP_TIMEOUT` is unreachable on this backend.

## Current test posture

`test/03_system/gpu_lane/cuda_debug_session_conformance_spec.spl` does NOT
skip the vector. It asserts the exact failure mode positively:

```
assert_false(devt.ok)
assert_equal(devt.error, "cuda-lane-device-timeout-sentinel")
assert_equal(shut_t, "cuda-lane-session-cleanup-pending")
```

so the spec goes RED the moment the conflation is fixed — which is precisely
when the full field-for-field diff should start running for this vector.
Whoever fixes this must delete that branch and let the vector fall through to
`_diff_device_vs_ref`.

## Suggested fix

Distinguish the two at the source. The VM budget sentinel is written by the
kernel *before* it returns normally, so a completed launch (fence/sync
succeeded) carrying `0xDEAD0000` is a budget expiry, not a hang; only a
launch that failed to complete is a true device timeout. Gate the
`completion_unknown` latch on the launch actually failing to complete, rather
than on the sentinel value alone.

# CUDA lane reads the SVM-G budget sentinel as a device timeout, making budget expiry unobservable to a debugger
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Triage 2026-09-13
Reconfirmed via source inspection: CUDA lane still conflates the SVM-G
budget sentinel with a device timeout per this record. GPU lane semantics
fix, needs CUDA hardware to verify safely; not attempted here. Left OPEN
(P2), no code change attempted.


## Fix evidence 2026-11-05 (work/libbug-std-cudasentinel-20261105)

Fixed in `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl`: the launch
outcome classification was factored into a pure, unit-testable helper
`classify_launch_outcome(launch_completed, sentinel_raw)`. A launch that
provably completed (sync succeeded) now returns success with the
completion latch OFF regardless of the arena sentinel -- the kernel writes
`SENTINEL_TIMEOUT` before returning normally on VM budget exhaustion, so a
completed launch carrying `0xDEAD0000` is a budget expiry that the caller
decodes from the readback arena (executor `_decode_sentinel` marks it
`timed_out`, making `DebugTarget`'s `STOP_TIMEOUT` reachable on this lane).
The `completion_unknown`/`release_pending` latch now fires only when the
launch actually failed to complete (sync failure) -- the deliberate
protection for a genuinely incomplete device launch is unchanged.

RED: new unit spec `test/01_unit/lib/gpu_lane/cuda_lane_budget_sentinel_spec.spl`
failed 3/3 pre-fix (`semantic: function 'classify_launch_outcome' not found`
-- the lane layer had no seam to report a completed budget sentinel as
anything but a device timeout). GREEN: same spec passes 3/3 post-fix.
The asserted-failure branch for the `budget_expiry_while_debugging` vector
was deleted from `test/03_system/gpu_lane/cuda_debug_session_conformance_spec.spl`
per this doc's instruction; the vector now falls through to
`_diff_device_vs_ref`.

Device qualification caveat: this host lists an NVIDIA GB10 GPU and
`CudaLaneSession.probe()` returns "", but every device spec (including the
pre-existing `cuda_jit_hello_spec` live row and `cuda_vm_executor_conformance_spec`)
fails at `cuda-lane-arena-guard-init-failed` (HtoD guard upload) both
before and after the fix -- an environment/driver limitation of the seed
binary on this host, identical pre/post. The live-device diff for the
budget vector still needs qualification on a host with a working CUDA
lane; the field-for-field expectations are unchanged and the host ref_vm
side of the diff is covered by `test/01_unit/lib/svmg/ref_vm_debug_spec.spl`.

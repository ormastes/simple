# BUG: CudaVmExecutor D3 conformance vectors hit `array index out of bounds: index is 0 but length is 0`

**Status:** OPEN
**Date filed:** 2026-08-08
**File:** `src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl` (SGP arena/log encoding path,
around `LOG_CAP_OFFSET`/arena construction, `cuda_vm_executor.spl:111` region)
**Severity:** MEDIUM — blocks live-device D3 conformance verification, now that
`doc/08_tracking/bug/cuda_lane_probe_misses_device_unavailable_2026-08-08.md` is
fixed and the session actually reaches this code on a real device.

## Symptom

On the same healthy two-GPU host (RTX A6000 + TITAN RTX) used to fix the sibling
device-identity bug, with `CudaLaneSession.init()` now succeeding:

```
bin/simple test test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl
✗ should skip cleanly, or run every conformance vector on a live device
  semantic: array index out of bounds: index is 0 but length is 0
2 examples, 1 failure
```

The sibling example ("should TRAP on call-stack overflow", 33 nested CALLs)
passes (1/1), so this is specific to the vector-execution path, not a blanket
session failure.

## Not yet root-caused

This was discovered as a direct consequence of fixing the device-identity bug
(previously the session never got far enough to reach this code — the spec was
0/2 for an unrelated reason). It has not yet been traced to a specific line;
the error text says a zero-length array/slice is being indexed at position 0
somewhere in the D3 vector dispatch or arena/log encoding path in
`cuda_vm_executor.spl`. Needs its own instrumented pass (print the array length
and call site immediately before the failing index) to pin down which
zero-length collection is being read.

## Reproduce

```
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_RUST_SEED_WARNING=0 bin/simple test \
  test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl --no-session-daemon
```

Do NOT close this by weakening any assertion — this is a legitimate RED per
`.claude/rules/testing.md`.

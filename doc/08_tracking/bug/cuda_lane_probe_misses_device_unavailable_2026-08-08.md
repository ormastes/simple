# BUG: CudaLaneSession.probe() does not detect device unavailability

**File:** `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl`  
**Line:** probe() method  
**Date filed:** 2026-08-08  
**Severity:** HIGH — device unavailability should be detected early

## Summary

CudaLaneSession.probe() returns "" (device available) even when the CUDA device is completely unavailable. This causes the executor's init() to proceed further and fail later with `'cuda-lane-device-identity-unavailable'`, which is less graceful than early device detection.

## Reproduction

1. Run CUDA VM executor conformance spec on a host without CUDA device support:
   - Vulkan hosts: VulkanLaneSession.probe() correctly returns "skip: ..." and the spec skips cleanly
   - CUDA hosts without device: CudaLaneSession.probe() returns "", then init() fails with device-identity error

2. Test file: `test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl` (lines 98-102)

## Expected behavior

CudaLaneSession.probe() should detect when device identity is unavailable and return a skip message, matching the contract of VulkanLaneSession.probe().

## Unblock condition

Fix CudaLaneSession.probe() to check device identity before returning "". Alternatively, update init() to convert device-identity-unavailable errors to skip messages at the session level.

## Current workaround

`test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl` lines 100-105 check init_err for `"device-identity-unavailable"` and skip gracefully. This workaround should be removed once the probe is fixed.

## Related issues

- `doc/08_tracking/bug/svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07.md` (same device vs. host semantics)

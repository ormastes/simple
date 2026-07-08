# CPU-SIMD/GPU Scheduling Parity Gate Missing

- **Date:** 2026-07-09
- **Status:** open
- **Severity:** high
- **Area:** Engine2D, CPU-SIMD, GPU scheduling

## Summary

Existing Engine2D tests cover backend ordering, lane selection, runtime queue
plumbing, and host/GPU queue readback separately. They do not yet prove that a
`cpu_simd` rendering workload and a GPU-backed workload preserve the same
queue/drain ordering or throughput invariants under the same backend override
contract.

## Evidence

Related proof paths include:

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_lane_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`
- `test/02_integration/lib/gpu/host_gpu_queue_roundtrip_spec.spl`
- `test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl`
- `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`

These are useful, but no dedicated spec compares `cpu_simd` and GPU scheduling
for the same drawing workload.

## Expected

Add a focused SPipe spec or wrapper that runs the same Engine2D workload through
explicit `cpu_simd` and GPU backend selections, then asserts queue submit,
completion, drain ordering, backend tag/config separation, fallback state, and
checksum/readback parity where the host GPU backend is available.

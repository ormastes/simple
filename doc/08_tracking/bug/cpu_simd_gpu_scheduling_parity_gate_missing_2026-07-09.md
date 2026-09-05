# CPU-SIMD/GPU Scheduling Parity Gate Missing

- **Date:** 2026-07-09
- **Status:** resolved
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

These are useful, but originally no dedicated spec compared `cpu_simd` and GPU
scheduling for the same drawing workload.

## Expected

Implemented by
`test/03_system/check/cpu_simd_gpu_scheduling_parity_spec.spl`. The spec keeps
`cpu_simd` on the host/direct drawing path and sends the same Draw IR payload
through the GPU pure queue, asserting queued -> submitted -> completed -> drained
ordering plus backend handle and payload hash/text preservation.

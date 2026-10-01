# GPU Scheduler Hardening and GPU-Resident Rendering NFRs

- **NFR-GPUSCH-001:** Bounded queue, payload, completion, and retirement
  capacity; queue-full never spins or allocates unboundedly.
- **NFR-GPUSCH-002:** Host service work is epoch/batch scale, never primitive
  scale for an admitted resident scene.
- **NFR-GPUSCH-003:** No per-frame full DOM/style/layout/DrawIR/pixel readback
  in the healthy strict resident loop.
- **NFR-GPUSCH-004:** Measurements report workload, backend/device identity,
  transfer bytes, host submissions, CPU service time, GPU timings, and
  p50/p95/p99 separately.
- **NFR-GPUSCH-005:** Reset, resize, cancellation, overflow, malformed input,
  and device loss fail closed with generation-safe retirement.

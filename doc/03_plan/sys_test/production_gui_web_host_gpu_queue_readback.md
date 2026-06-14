# Production GUI/Web Host-GPU Queue Readback System Test Plan

## Scope

Prove the production GUI/web host-GPU path with fail-closed evidence:

- `rt_host_gpu_queue_emit` records queue packets.
- `rt_host_gpu_queue_drain` distinguishes backend-code `0` unavailable packets from nonzero backend-code packets.
- Vulkan and CUDA readback wrappers pass where available.
- Metal and ROCm are reported as host-unavailable or runtime-unavailable with concrete reasons on Linux.

## Acceptance Criteria

- Queue emission is not treated as backend-capable submit by itself.
- `backend_code=0` drains as typed unavailable and cannot produce a production PASS.
- A nonzero backend-code drain may pass only the queue emit/drain subcheck; it is not evidence of backend-handle integration.
- Vulkan and CUDA child readback wrappers are reported as PASS where available, or host-unavailable/runtime-unavailable with the child reason when absent.
- Metal and ROCm are recorded as host-unavailable on this Linux lane unless their required host runtime and tools are present.
- Backend runtime queue integration may PASS only after a packet drains with a concrete nonzero backend runtime handle, not only an interpreter/fallback queue token.
- The report calls out Rust/C capacity parity and `SUBMITTED` status contract gaps when they remain present.
- The wrapper exits nonzero until the concrete backend-handle integration criterion is met, even when queue emit/drain and available backend readback wrappers pass.

## Evidence Command

```bash
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

The command is intentionally fail-closed until backend runtime queue integration is proven with a real Vulkan/CUDA handle.

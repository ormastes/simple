# GPU Scheduler Hardening and GPU-Resident Rendering Requirements

## Selected requirements

- **REQ-GPU-SCHED-ASYNC-001:** GPU DrawIR work uses the existing bounded queue and
  canonical terminal-completion model; normal submission does not immediately
  drain/complete the packet.
- **REQ-GPU-SCHED-LIFE-001:** Deferred operations preserve one terminal result and
  reject stale, invalid, full, reset, or duplicate-completion transitions.
- **REQ-GPU-SCHED-PAYLOAD-001:** The production hot path has a registered packed payload
  seam; text SDN remains an explicitly named compatibility/diagnostic path.
- **REQ-GPU-SCHED-PROFILE-001:** A strict GPU-scene profile rejects unsupported semantic
  work rather than silently falling back to CPU execution.
- **REQ-GPU-SCHED-PROOF-001:** GPU residency evidence distinguishes submission,
  execution, retirement, presentation, and display; source contracts do not
  satisfy hardware claims.
- **REQ-GPU-SCHED-SAFE-001:** Invalid, unavailable, or oversized deferred
  routes fail closed before commit.
- **REQ-GPU-SCHED-SAFE-002:** Completion-capacity exhaustion rejects admission
  without hidden drain or unbounded allocation.

## Added 2026-09-05 (all five plan steps implemented; device-gated verification)

- **REQ-GPU-SCHED-EPOCH-001:** One common epoch contract (`common.gpu.engine2d.gpu_epoch`)
  carries queue, operation, scene, surface and arena generations separately, a
  SimpleRing token/lease, and four independent truth labels (semantic residency,
  data residency, submission autonomy, scheduling assurance).
- **REQ-GPU-SCHED-PAYLOAD-002:** The packed generation store hashes rows
  incrementally as binary; no growing canonical text on the hot path.
- **REQ-GPU-SCHED-RESIDENT-001:** A fixed-arena Vulkan resident-2D slice submits N
  frames with zero per-frame semantic rebuilds and zero readbacks.
- **REQ-GPU-SCHED-RESIDENT-002:** Device evidence records binary identity, device
  and driver identity, monotonic host timestamps, transfer bytes and a negative
  control; device timestamps are reported unavailable until a query-pool extern exists.
- **REQ-GPU-SCHED-ISLAND-001:** The declared Web/GUI event/style/layout/render
  islands carry capability labels; required profiles refuse unsupported islands
  with the exact missing capability bits and never route them to CPU semantics.
- **REQ-GPU-SCHED-PROVIDER-001:** Vulkan, Metal and DirectX (D3D11 via DXVK; no
  D3D12 exists in the tree) providers are graded by one conformance contract:
  unavailable, routing_only, or full. No provider is graded full until it
  exposes a fence token and distinct submit/finish/complete/retire phases.
- **REQ-GPU-SCHED-AUTONOMY-001:** Autonomous (device-initiated) submission is
  allowed only for the `device_initiated_experimental` profile on a fully
  conformant provider that reports DGC/ICB/work-graph capability.
- **REQ-GPU-SCHED-VERIFY-001:** Every device-dependent verification spec skips
  green without `SIMPLE_GPU_TEST=1` and a present device, and runs unchanged
  when both are present.

## Still out of scope

Complete HTML/CSS/JavaScript GPU execution, a persistent kernel, device-
initiated OS I/O, a D3D12 provider, and universal latency claims.

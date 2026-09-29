<!-- codex-research -->
# Simple 2D and web renderer GPU optimization NFRs

Selected: NFR Target 1 — strict interactive.

- NFR-GPUUI-001: Warm device-present p95 is at most 12.5 ms at 3840x2160 for
  the shared showcase on a named admitted device/profile.
- NFR-GPUUI-002: Simple/C Vulkan p95 is at most 2.0x when workload, timing
  boundary, device, readback mode, warmups, and samples match.
- NFR-GPUUI-003: Chrome/Simple ratios are emitted only when both sides are
  measured with identical interval metadata and verified GPU identity.
- NFR-GPUUI-004: Steady display performs zero timed framebuffer readback;
  correctness uses at most one explicit readback per captured sample.
- NFR-GPUUI-005: Two or three frames may be in flight without an unconditional
  CPU fence wait; completion is backed by a real device fence/timeline receipt.
- NFR-GPUUI-006: Renderer memory stabilizes after warmup, reports retained
  allocations/bytes, and returns to the documented bound after teardown.
- NFR-GPUUI-007: Evidence records viewport, backend/device, source and binary
  revisions, fallback, p50/p95, RSS, upload/readback bytes, fence completion,
  damage area, and checksum/readback proof.

# SimpleOS QEMU Host-GPU 2D Requirements

**Selected option:** Feature B — cross-host QEMU GPU service.

**Selected extension (2026-07-26):** share the same Engine2D/evidence contract
across Linux/macOS/Windows QEMU and UNO Q, VisionFive 2, and UP Squared native
board adapters; do not duplicate Simple 2D or backend public APIs.

## Requirements

- REQ-001: One architecture-neutral guest protocol shall carry Simple drawing and portable-processing batches on x86_64, AArch64, and RISC-V without architecture-specific public APIs.
- REQ-002: The guest shall negotiate protocol version, maximum batch/payload sizes, rendering backends, processing backends, readback support, and host-service readiness before submitting work.
- REQ-003: Rendering requests shall reuse Engine2D/Draw IR semantics and select Vulkan, Metal, or DirectX only when the host service provides strict device-backed evidence for that backend.
- REQ-004: Processing requests shall use one minimal ProcessingIR-compatible contract and select Vulkan, CUDA, Metal, or CPU below it; backend names shall not create public API forks.
- REQ-005: Every submitted batch shall have a unique run/frame identity, bounded commands and buffers, a completion status, backend/reason fields, timing counters, and a correlated output checksum.
- REQ-006: Device-backed rendering shall return same-frame readback with a positive native backend handle and exactly match the CPU oracle; guest backing, upload-only, screenshots, configured flags, and synthetic handles shall not pass.
- REQ-007: Device-backed processing shall return a result buffer exactly matching the CPU oracle and a correlated host completion receipt; compile-only artifacts shall not pass.
- REQ-008: Vulkan shall be supported on prepared Linux hosts, Metal on prepared macOS hosts, DirectX on prepared Windows hosts, and CUDA on prepared NVIDIA hosts; missing host support shall produce `unsupported` or `blocked` with a stable reason.
- REQ-009: If the host service or requested backend is unavailable, SimpleOS shall remain bootable and select the existing software/CPU path without falsely reporting acceleration.
- REQ-010: The host service shall reject unknown protocol versions, oversized payloads, invalid dimensions, out-of-range buffer references, unsupported operations, duplicate completions, and stale frame identities.
- REQ-011: One canonical wrapper shall report per-host/per-architecture rows as `pass`, `unsupported`, `blocked`, or `fail`, and shall feed the existing SimpleOS hardening matrix without weakening its 26/26 contract.
- REQ-012: SPipe scenarios and their generated Markdown manual shall cover negotiation, rendering parity, processing parity, fallback, malformed input, stale receipts, and fail-closed evidence parsing for all three guest architectures.
- REQ-013: Linux, macOS, and Windows QEMU rows shall reuse one
  `SimpleOsGuestGpuTransport`, session protocol, parity artifact, receipt, and
  evidence ladder; host API and resource-interoperability differences shall
  remain private to `HostGpuAdapter`.
- REQ-014: Default VirtIO-GPU 2D scanout shall be classified as
  `presentation-only` with CPU/SIMD rendering. Virgl, Venus, and rutabaga shall
  be admitted only after the exact host and SimpleOS guest transport
  prerequisites are observed.
- REQ-015: UNO Q, VisionFive 2, and UP Squared shall reuse the same
  Draw IR/Engine2D backend lane and parity receipt through
  `NativeBoardGpuAdapter`; each board owns only firmware, memory mapping,
  submission, fence, readback, display, and boot/deployment integration.
- REQ-016: The extension shall not change `DrawIrComposition`,
  `RenderBackend`, existing Metal/Vulkan backend selection, font ownership,
  event propagation, or CPU/software fallback semantics.
- REQ-017: Every compared rendering artifact shall record logical
  `0xAARRGGBB` format, byte serialization, dimensions, stride, DPI, alpha
  semantics, color-space policy, byte length, backend/device identity,
  run/frame/submission/readback IDs, and SHA-256.
- REQ-018: A physical-board pass shall include board identity, boot/download
  path, SimpleOS serial or SSH transcript, GPU/firmware identity, submission
  and fence evidence, and device-origin readback exactly matching the CPU SIMD
  oracle.
- REQ-019: Vendor Linux drivers, Mesa utilities, marketing API versions, and
  host-side screenshots are readiness evidence only. They shall not prove
  SimpleOS native-board acceleration.
- REQ-020: Unsupported upstream driver/device combinations shall remain visible
  as `unsupported` or `blocked` with an exact prerequisite and resume command;
  they shall never be dropped, skipped, or counted as PASS.

## Scope

Direct VFIO/vendor guest drivers and a full guest Vulkan implementation are excluded. Shared memory is deferred until the selected NFR measurements show the bounded channel transport is insufficient.

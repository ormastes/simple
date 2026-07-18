# SimpleOS QEMU Host-GPU 2D Requirements

**Selected option:** Feature B — cross-host QEMU GPU service.

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

## Scope

Direct VFIO/vendor guest drivers and a full guest Vulkan implementation are excluded. Shared memory is deferred until the selected NFR measurements show the bounded channel transport is insufficient.


<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D System Test Plan

## Contract

Canonical wrapper: `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`.
Canonical spec: `test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl`.
Rows are `{linux,macos,windows} × {x86_64,aarch64,riscv64}` and report only
`pass`, `unsupported`, `blocked`, or `fail` with a stable reason.

## Coverage

| Scenario | Requirements |
|---|---|
| negotiate one bounded architecture-neutral protocol | REQ-001,002,005 |
| exact device-backed Draw IR readback | REQ-003,006; NFR-001 |
| checked raw Vulkan CLEAR/RECT completion and fail-closed provenance | REQ-003,005,006,010; NFR-001 |
| exact device-backed ProcessingIR result | REQ-004,007; NFR-002,004 |
| honest cross-host backend classification | REQ-008,009 |
| malformed and stale input rejection | REQ-010; NFR-007 |
| multi-ISA row aggregation and fail-closed parsing | REQ-011,012; NFR-008,009 |
| latency, negotiation, and RSS evidence | NFR-003,005,006 |

## Evidence Rules

The wrapper must boot the target guest, capture guest negotiation/submission,
capture the host daemon device receipt, and correlate IDs and checksums. A row
cannot pass from QEMU flags, QMP screenshots, VirtIO-GPU scanout, synthetic
handles, compile-only output, or a CPU mirror. Unsupported and blocked rows are
valid classifications but do not satisfy a host/ISA combination classified as
supported.

The focused Vulkan unit boundary renders CLEAR plus solid RECT on a real or
lavapipe device and requires exact pixels, `device_readback`, a positive
handle, and no fallback/unknown-completion state. The system spec also rejects
the old unchecked submit route structurally so an ignored SFFI result cannot
silently regain receipt eligibility.

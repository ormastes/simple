<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D Architecture

## Decision

Use one bounded, architecture-neutral guest/host protocol over an existing
VirtIO serial channel. The guest submits Draw IR or ProcessingIR payloads; a
host daemon selects Vulkan, Metal, DirectX, CUDA, or CPU and returns a
correlated receipt plus output. x86_64, AArch64, and RISC-V adapters only own
boot/device discovery. They must not define backend-specific public APIs.

Shared memory and VFIO are excluded until measured channel copies violate the
selected NFRs. VirtIO-GPU scanout remains display transport and is not evidence
of device-backed execution.

## Virtual Capsule

`SimpleOsHostGpuSession` is the capsule boundary:

1. negotiate a version and bounded capabilities;
2. submit one immutable rendering or processing batch;
3. validate the matching completion receipt;
4. expose backend/reason, native device identity, timing, RSS, and checksums;
5. select existing CPU/software fallback on unavailable or invalid service.

The capsule composes existing Engine2D/Draw IR and ProcessingIR. Host backend
adapters are private children. No feature transform or new public GPU API is
needed.

## Trust and Evidence Boundary

The host daemon rejects unknown versions, oversized batches, invalid geometry
or buffer references, unsupported operations, duplicate completions, and stale
run/frame IDs before allocation or execution. A device-backed pass requires a
positive native backend handle, host device identity, matching request and
receipt IDs, same-frame readback/result bytes, exact CPU-oracle checksum, and
backend markers from the host adapter. Flags, screenshots, scanout, CPU mirrors,
and synthetic handles fail closed.

## Platform Classification

| Host | Rendering | Processing | Classification rule |
|---|---|---|---|
| Linux | Vulkan | Vulkan; CUDA on prepared NVIDIA host | pass only with device receipt |
| macOS | Metal | Metal | pass only with Metal device receipt |
| Windows | DirectX or Vulkan | DirectX/Vulkan | pass only with device receipt |
| Any missing prerequisite | CPU/software | CPU | `unsupported` or `blocked`, never accelerated |

Cross-ISA TCG rows prove protocol correctness and provenance, not native-ISA
latency. The first implementation slice is x86_64 Linux Vulkan; the same wire
contract is reused unchanged for AArch64 and RISC-V.


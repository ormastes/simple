<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D Architecture

## Decision

Use one bounded, architecture-neutral guest/host protocol over QEMU
`ivshmem-plain`. The current guest submits a bounded canonical plain-RECT Draw
IR payload and a bounded ProcessingIR `FillU32` payload. The production x86
desktop source path routes local frames through `DrawIrComposition`, resolved top-level
`WmContentFrame` IMAGE resources, and Engine2D; styled text/image attachments
remain required before that same complete composition may use host offload. A
host daemon selects a supported private backend and
returns a correlated receipt plus output. x86_64, AArch64, and RISC-V adapters
only own boot/device discovery. They must not define backend-specific public
APIs.

The fixed 8 MiB shared region carries control, bounded payload, and readback;
VFIO remains excluded. VirtIO-GPU scanout remains display transport and is not
evidence of device-backed execution.

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

Vulkan ProcessingIR hashes the runtime-selected driver identity, which includes
device name, vendor/device IDs, driver version, and API version. Storage-buffer handles remain per-request resource handles and
must never be reused as device provenance. Vulkan processing is negotiated only
after a bounded real ProcessingIR probe returns both values.

## Platform Classification

| Host | Rendering | Processing | Classification rule |
|---|---|---|---|
| Linux | Vulkan | Vulkan; CUDA on prepared NVIDIA host | pass only with device receipt |
| macOS | Metal implementation, native receipt still required | unavailable: no Metal ProcessingIR executor | never infer processing from an Engine2D clear |
| Windows | unavailable: current Simple DirectX lane is software emulation | unavailable | standalone D3D probes are not production receipts |
| Any missing prerequisite | CPU/software | CPU | `unsupported` or `blocked`, never accelerated |

Cross-ISA TCG rows prove protocol correctness and provenance, not native-ISA
latency. The first implementation slice is x86_64 Linux Vulkan; the same wire
contract is reused unchanged for AArch64 and RISC-V.

`src/os/compositor/engine2d_wm_frame_executor.spl` is the local production
fallback owner. It builds and submits the canonical Simple-owned composition,
resolves only
unique checksum-valid top-level IMAGE resources, and rejects unsupported nested
frames rather than dropping their pixels. Host offload must extend the bounded
wire with equivalent attachments; it must not reintroduce a full-frame copy.
The canonical Draw IR SDN skin preserves the complete typed command metadata,
so styled RECT/TEXT and IMAGE semantics can cross the wire without a producer-
specific parallel codec; binary image pixels remain separate bounded resources.
The core executor imports `draw_ir_adv.spl`; host runtime-queue integration is
kept in the sibling `draw_ir_runtime_adv.spl` so the baremetal closure does not
acquire direct host-runtime APIs. This source path is not compile-verified while
TODO 548 blocks the pure-Simple checker.

The QEMU build owner accepts only a runnable pure-Simple compiler. A candidate
whose version probe identifies it as a bootstrap seed is rejected, and absence
of a valid compiler fails the build before spawning any architecture worker.

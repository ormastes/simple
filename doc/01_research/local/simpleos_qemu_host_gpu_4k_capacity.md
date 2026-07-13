<!-- codex-research -->
# SimpleOS QEMU Host-GPU 4K Capacity — Local Research

## Scope

Determine how the existing architecture-neutral `ivshmem-plain` protocol can
carry an exact 3840x2160 ARGB frame and IMAGE resources on x86_64, AArch64,
and RISC-V without cropping, downscaling, unbounded allocation, or false GPU
provenance.

## Current Capacity

`src/lib/common/gpu/simpleos_host_gpu_protocol.spl` owns the fixed layout:

- region: 8,388,608 bytes;
- control: 4,096 bytes;
- payload: 65,536 bytes;
- readback/resource arena: 8,318,976 bytes.

Exact ARGB requirements:

| Frame | Bytes | Current result |
|---|---:|---|
| 1280x720 | 3,686,400 | fits |
| 1920x1080 | 8,294,400 | fits with 24,576-byte margin |
| 3840x2160 | 33,177,600 | rejected |
| 4096x4096 | 67,108,864 | rejected |

A 32 MiB region leaves 33,484,800 bytes after control and payload, enough for
one 3840x2160 frame or one full-frame IMAGE resource plus its bounded header
and URI. IMAGE resources and output reuse the same arena: the daemon snapshots
validated resources before writing output, so required capacity is the larger
of total resources and output, not their sum. Multiple large window resources
can still exceed 32 MiB and must select local fallback.

## Owners and Call Chain

- Layout, maxima, negotiation validation:
  `src/lib/common/gpu/simpleos_host_gpu_protocol.spl`
- Draw IR and IMAGE resource codec:
  `src/lib/common/gpu/simpleos_host_gpu_draw_ir.spl`
- Host file mapping and execution:
  `src/app/simpleos_gpu_host/main.spl`
- Guest request/receipt bridge:
  `src/os/lib/gpu_bridge/host_gpu_ivshmem.spl`
- Guest PCI BAR discovery/programming:
  `src/os/kernel/ipc/host_gpu_ivshmem_map.spl`
- Shared three-ISA probe:
  `examples/09_embedded/simple_os/arch/common/host_gpu_ivshmem_probe_entry.spl`
- QEMU shared file/device lifecycle:
  `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`

## Cross-ISA Mapping Constraints

- The mapper currently requires BAR2 size exactly 8 MiB and assigns device
  windows at 16 MiB strides.
- x86_64 reserves a 1 GiB direct-boot window, sufficient for a deliberately
  assigned 32 MiB BAR after stride/range changes.
- AArch64 fixes the BAR at `0x3e000000`; growing it to 32 MiB reaches
  `0x40000000`, the kernel/RAM boundary. The BAR must move to a separately
  owned non-overlapping PCI MMIO window.
- RISC-V reserves `0x60000000..0x80000000` (512 MiB). Thirty-two possible PCI
  device IDs cannot each receive a 32 MiB slot. The mapper must own one bounded
  ivshmem window or reject unsupported device placement; multiplying the old
  per-device formula is invalid.

## Compatibility

The offsets can remain stable, but silently enlarging protocol v1 is not mixed-
binary compatible. Old guests require an 8 MiB BAR and reject a larger
negotiated maximum; an old daemon cannot map or advertise the larger region.
A fixed-size change therefore needs protocol v2 and coordinated peers, while a
negotiated design may retain explicit v1=8 MiB compatibility.

## Verification Surface

Required evidence includes 720p regression, exact 4K, capacity boundary and
one-byte overflow rejection, malformed/overflow dimensions, corrupt checksum,
stale generation, a full IMAGE resource, peer-version behavior, all three Linux
guest ISAs, native latency/RSS, and honest unsupported rows elsewhere.

Fresh execution remains blocked by TODO 548's crashing deployed self-hosted
compiler. No Rust-seed fallback is permitted.

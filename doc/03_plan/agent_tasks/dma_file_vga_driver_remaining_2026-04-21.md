# DMA, File Driver, and VGA/Display Driver Remaining Plan

Status: open
Last updated: 2026-04-21
Scope: shared DMA ownership, SR-IOV/IOMMU isolation, file/block direct I/O,
legacy VGA/BGA framebuffer acceleration, and VirtIO-GPU DMA transfer paths.

Related feature requests:
- `doc/08_tracking/feature_request/net_acceleration_requests.md`
  - `FR-NET-0008` shared DMA with storage/display
  - `FR-NET-0009` SR-IOV and DMA isolation gating
- `doc/08_tracking/feature_request/driver_framework_requests.md`
  - `FR-DRIVER-0009` shared DMA descriptor contract
  - `FR-DRIVER-0010` DMA-backed file/block direct I/O
  - `FR-DRIVER-0011` VGA/BGA and VirtIO-GPU acceleration boundary

Relevant code:
- `src/os/userlib/device.spl`
- `src/os/kernel/ipc/syscall.spl`
- `src/os/kernel/lifecycle/task_cleanup.spl`
- `src/os/drivers/nvme/`
- `src/os/drivers/virtio/virtio_blk.spl`
- `src/os/drivers/framebuffer/`
- `src/os/drivers/virtio/virtio_gpu.spl`
- `src/os/kernel/memory/vmm.spl`

## Current Baseline

- DMA syscalls exist: allocate/free DMA buffers through syscall handlers.
- `src/os/userlib/device.spl` exposes `DmaAllocResult` and
  `SharedDmaBuffer`.
- Task cleanup tracks DMA buffers as kernel-owned resources.
- VirtIO-GPU already has DMA concepts for command/response buffers.
- BGA/framebuffer init exists for QEMU display fallback.
- NVMe and VirtIO-BLK drivers exist, but no common direct-I/O DMA extension is
  documented across VFS/file-driver surfaces.

## P0 - Shared DMA Safety Contract

1. Promote one canonical DMA descriptor.
   - Feature request: `FR-DRIVER-0009`
   - Files:
     - `src/os/userlib/device.spl`
     - `src/os/kernel/ipc/syscall.spl`
     - `src/os/kernel/lifecycle/task_cleanup.spl`
   - Acceptance:
     - Descriptor includes virtual address, physical address, device address,
       byte length, cache policy, owner task, and owner device/function.
     - Release path validates owner, size, and allocation identity.
     - Task cleanup releases all leaked DMA buffers deterministically.

2. Add cache policy and synchronization helpers.
   - Feature request: `FR-DRIVER-0009`
   - Acceptance:
     - Coherent, uncached, write-combining, and flush-required memory kinds are
       represented explicitly.
     - CPU-to-device and device-to-CPU synchronization helpers exist even when
       they are no-ops on coherent platforms.
     - Tests cover no-op coherent path and explicit flush-required path.

3. Gate DMA and SR-IOV on isolation state.
   - Feature requests: `FR-NET-0009`, `FR-DRIVER-0009`
   - Acceptance:
     - Device grant records isolation domain or explicit no-isolation mode.
     - SR-IOV VF assignment fails closed without IOMMU or equivalent isolation.
     - No-IOMMU trusted-driver mode does not advertise isolated acceleration.

## P1 - File and Block Driver DMA Direct I/O

1. Add direct-I/O extension to file driver interface.
   - Feature request: `FR-DRIVER-0010`
   - Files:
     - `doc/05_design/fs_driver_interface.md`
     - `src/lib/nogc_sync_mut/fs_driver/`
     - VFS service call boundary
   - Acceptance:
     - File APIs expose explicit direct I/O capability or extension.
     - Buffered read/write remains default.
     - Direct I/O requires caller-owned DMA buffer and documented alignment.

2. Wire block backends.
   - Feature request: `FR-DRIVER-0010`
   - Files:
     - `src/os/drivers/nvme/`
     - `src/os/drivers/virtio/virtio_blk.spl`
   - Acceptance:
     - NVMe queues can submit DMA-backed read/write commands.
     - VirtIO-BLK can submit DMA-backed requests using the same descriptor.
     - Timeout and completion errors propagate to the direct-I/O caller.

3. Add direct-I/O tests and benchmark.
   - Acceptance:
     - Tests cover aligned read/write, unaligned handling, timeout, and cleanup
       on task exit.
     - Benchmark compares buffered copy path with direct DMA path on the same
       fixture and reports latency, throughput, and RSS.

## P1 - VGA/BGA and VirtIO-GPU Display Acceleration

1. Split display capability naming.
   - Feature request: `FR-DRIVER-0011`
   - Files:
     - `src/os/drivers/framebuffer/`
     - `src/os/drivers/virtio/virtio_gpu.spl`
     - display service init path
   - Acceptance:
     - Capability summary distinguishes `framebuffer-mmio`,
       `bga-write-combining`, and `virtio-gpu-dma`.
     - Legacy VGA/BGA is not labeled as DMA acceleration.

2. Add dirty-rectangle flushing for BGA/framebuffer path.
   - Feature request: `FR-DRIVER-0011`
   - Acceptance:
     - Display service can mark damaged rectangles.
     - Flush path bounds work to changed regions when backend supports it.
     - Full-frame fallback remains available.

3. Move VirtIO-GPU transfers to shared DMA descriptor.
   - Feature request: `FR-DRIVER-0011`
   - Acceptance:
     - Resource attach, transfer-to-host, and flush commands use the canonical
       DMA descriptor.
     - Command and response DMA buffers use the same allocation and cleanup
       rules as net/storage.
     - QEMU display tests cover both BGA fallback and VirtIO-GPU DMA path when
       enabled.

## P2 - Cross-Subsystem Performance Proof

1. Add a shared acceleration benchmark report.
   - Acceptance:
     - Network: request latency and throughput.
     - File/block: buffered vs direct DMA read/write.
     - Display: full-frame vs dirty-rectangle flush cost.
     - Each result includes backend capability summary and isolation mode.

2. Add failure-mode tests.
   - Acceptance:
     - Wrong-owner DMA free fails.
     - Device tries to use DMA buffer assigned to another function: rejected.
     - SR-IOV requested without isolation: rejected.
     - Display DMA backend unavailable: falls back to framebuffer path.

## Verification Gates

Every implementation wave must run:

- Focused unit specs for touched modules.
- `git diff --check`.
- Touched-file stub scan for `TODO`, `pass_todo`, `stub`, `placeholder`,
  `not implemented`, and `expect(true).to_equal(true)`.
- QEMU scenario for the changed device class when applicable.
- `sh scripts/check-core-runtime-smoke.shs bin/simple` after `src/lib` changes.
- `SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs` after
  compiler/core/lib changes that can affect MCP/LSP startup.

## Guardrails

- Do not expose SR-IOV to user-space without isolation.
- Do not advertise legacy VGA/BGA as DMA-capable.
- Do not add private DMA descriptor shapes for individual drivers when the
  shared descriptor can model the transfer.
- Do not treat performance as improved unless fallback correctness, timeout
  behavior, and cleanup are also verified.

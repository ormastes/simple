<!-- codex-research -->
# Driver DMA Direct I/O Local Research

Feature: FR-DRIVER-0010.

## Findings

- `Capability.DirectIo` already exists in `std.fs_driver.capability` and is the
  opt-in gate for direct I/O.
- `DirectIoExt` in `std.fs_driver.extension` validates caller-owned
  `SharedDmaBuffer` alignment and fails closed by default.
- `std.io.dma.SharedDmaBuffer` is the canonical cross-driver descriptor with
  CPU, host physical, device-visible addresses, cache policy, owner, and
  allocation id.
- NVMe already has sector submission methods that take a physical DMA address:
  `read_sectors_notify` and `write_sectors_notify`.
- VirtIO-BLK already has transport DMA support, but the safe direct caller path
  must keep VirtIO request header/status scratch memory driver-owned and point
  only the payload descriptor at the caller buffer.
- VFS IPC remains buffered-only. Direct I/O should stay below VFS IPC until
  handle-to-mount routing is tightened.

## Decision

Implement a direct-I/O request/result model in the fs-driver layer, add
SharedDmaBuffer-backed NVMe and VirtIO-BLK adapter methods, and keep buffered
file APIs as the default path.

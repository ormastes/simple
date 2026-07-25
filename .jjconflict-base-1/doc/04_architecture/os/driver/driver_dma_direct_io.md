# Driver DMA Direct I/O Architecture

Feature: FR-DRIVER-0010.

## Layers

- `std.io.dma` owns the canonical descriptor and release authority contract.
- `std.fs_driver.extension.DirectIoExt` owns capability metadata and alignment
  validation.
- `std.fs_driver.direct_io` owns the request/result model used by file and
  block direct-I/O callers.
- NVMe and VirtIO-BLK own hardware submission. They accept
  `SharedDmaBuffer`, perform device-specific validation, and submit directly to
  existing queues.

## Driver Boundaries

NVMe maps directly to PRP1 via `buf.device_addr`.

VirtIO-BLK uses driver-owned scratch DMA for the request header and status
byte; only the payload descriptor points to the caller-owned DMA buffer. This
keeps transport layout private to the VirtIO driver.

## Deferred

VFS IPC methods for `READ_DMA`/`WRITE_DMA` are deferred until fd-to-mount
routing is made precise enough to avoid widening the current buffered routing
shortcut.

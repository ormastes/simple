# Driver DMA Direct I/O Agent Tasks

Feature: FR-DRIVER-0010.

## Completed Work Split

- Explorer: locate existing fs-driver, DMA, NVMe, VirtIO-BLK, and SPipe
  patterns.
- Codex implementation: add common direct-I/O request/result model, NVMe and
  VirtIO SharedDmaBuffer adapter methods, system spec, and tracker updates.

## Follow-Up Candidates

- Add VFS IPC `READ_DMA` and `WRITE_DMA` after handle-to-mount routing is
  precise.
- Extend NVMe direct I/O beyond PRP1-sized aligned transfers with PRP2/list
  support.
- Add hardware-backed QEMU coverage for VirtIO-BLK direct payload descriptors.

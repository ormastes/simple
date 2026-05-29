# FR-DRIVER-0009 Local Research — Shared DMA Descriptor Contract

Status: implemented research note.

Existing surfaces already had most of the requested descriptor data:

- `src/lib/nogc_sync_mut/io/dma.spl` defines `SharedDmaBuffer`, `DmaOwner`, `DmaCachePolicy`, and sync helpers.
- `src/os/userlib/device.spl` defines syscall-facing `DeviceDmaDescriptor` and cache policy constants.
- `src/os/kernel/ipc/syscall.spl` records task owner, owner device, size, cache policy, and allocation id for DMA allocations, and `_handle_free_dma` rejects unknown, wrong-owner, wrong-device, and wrong-size frees.
- `src/lib/nogc_sync_mut/fs_driver/extension.spl` had a narrower `DirectIoBuffer`, so file/block direct I/O did not yet accept the canonical descriptor directly.

Implementation conclusion: keep `std.io.dma.SharedDmaBuffer` as the cross-driver shape, add pure release-authority validation for unit/system coverage, wire userlib device-owned free through the existing syscall owner-device parameter, and let Direct I/O validate `SharedDmaBuffer` directly while preserving the older buffer entry points.

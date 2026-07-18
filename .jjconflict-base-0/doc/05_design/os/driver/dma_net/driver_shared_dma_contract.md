# FR-DRIVER-0009 Design — Shared DMA Descriptor Contract

Canonical descriptor:

- `std.io.dma.SharedDmaBuffer`
- Fields: CPU virtual address, host physical address, device-visible address, byte length, explicit cache policy, owner task/BDF, allocation id.

Release validation:

- `DmaReleaseRequest` carries requester task, requester BDF, requested byte length, allocation id, and whether the allocation has already been released.
- `validate_shared_dma_release` rejects invalid descriptors, double release, size mismatch, allocation-id mismatch, wrong task, and wrong BDF before allocator teardown.

Syscall integration:

- Kernel syscall 84 already records caller task, owner device, rounded size, cache policy, and allocation id.
- Kernel syscall 85 already rejects unknown allocation, wrong caller task, wrong owner device, and wrong size.
- `free_device_dma` now passes the descriptor owner device to syscall 85 so userlib does not bypass the kernel's device-owner check.

File/block integration:

- `DirectIoExt.validate_shared_buffer`, `read_shared_dma`, and `write_shared_dma` accept `std.io.dma.SharedDmaBuffer` directly.
- Legacy `DirectIoBuffer` remains available for compatibility, but new code can use the canonical descriptor without private ownership fields.

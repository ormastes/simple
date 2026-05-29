# FR-NET-0008 Local Research — Shared DMA Buffer Ownership

Status: implemented research note.

Relevant implementation:

- `std.io.dma.SharedDmaBuffer` is the canonical descriptor with CPU address, host physical address, device-visible address, byte length, cache policy, owner task/BDF, and allocation id.
- `std.io.dma.validate_shared_dma_release` covers double-free, wrong-size, wrong-task, wrong-device, and allocation-id mismatch checks.
- `std.fs_driver.extension.DirectIoExt` accepts `SharedDmaBuffer` directly for file/block direct I/O.
- `std.io.packet_io.PacketDmaLease` now carries `SharedDmaBuffer` for network RX/TX packet rings.
- Display/GPU transfer buffers are represented by the same std descriptor shape in the system coverage; the syscall-facing `os.userlib.device` type remains a separate ABI-safe wrapper.

Conclusion: FR-NET-0008 can be closed by tying packet I/O leases and file/block direct I/O to the shared DMA contract that was introduced for FR-DRIVER-0009, while preserving explicit display transfer coverage with the same descriptor shape.

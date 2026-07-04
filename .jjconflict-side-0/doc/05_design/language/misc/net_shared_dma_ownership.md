# FR-NET-0008 Design — Shared DMA Buffer Ownership

Canonical descriptor:

- `std.io.dma.SharedDmaBuffer` is the shared descriptor for network, file/block, and display/GPU handoff.
- Ownership is represented by `DmaOwner` plus `allocation_id`.
- Cache behavior is represented by `DmaCachePolicy`.

Network API:

- `PacketDmaLease` wraps a `SharedDmaBuffer` for packet-ring RX/TX ownership.
- `packet_rx_dma_lease` and `packet_tx_dma_lease` hand the DMA buffer to the application.
- `packet_dma_complete` returns ownership to the driver.

Storage API:

- `DirectIoExt.validate_shared_buffer`, `read_shared_dma`, and `write_shared_dma` accept `SharedDmaBuffer` directly.

Display transfer coverage:

- Display/GPU transfer buffers use the same `SharedDmaBuffer` descriptor shape in cross-driver tests.
- The syscall-facing `os.userlib.device` descriptor remains ABI-local and is not imported into the std packet API to avoid a cross-layer name collision.

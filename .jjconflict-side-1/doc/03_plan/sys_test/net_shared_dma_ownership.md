# FR-NET-0008 System Test Plan — Shared DMA Buffer Ownership

System spec: `test/system/net_shared_dma_ownership_spec.spl`

Coverage:

- Network packet RX/TX DMA leases carry `std.io.dma.SharedDmaBuffer`.
- File/block direct I/O validates the same descriptor.
- Display transfer buffers are represented with the same shared std descriptor shape.
- Shared release validation rejects double-free and wrong-size release.
- Cache sync helpers are exercised before packet completion.

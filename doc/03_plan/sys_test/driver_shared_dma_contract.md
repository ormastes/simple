# FR-DRIVER-0009 System Test Plan — Shared DMA Descriptor Contract

System spec: `test/system/driver_shared_dma_contract_spec.spl`

Coverage:

- Network, file/block, and display-style consumers are represented by the same `std.io.dma.SharedDmaBuffer` shape.
- The four explicit cache policies are constructible and accepted by shared sync helpers.
- Release validation accepts matching task, BDF, size, and allocation id.
- Release validation rejects double-free, wrong-size free, wrong-task free, and wrong-device free.
- `DirectIoExt` validates `SharedDmaBuffer` directly for block/file DMA alignment.

The kernel syscall table already enforces owner task, owner device, and rounded allocation size in `_handle_free_dma`; the system spec covers the portable descriptor contract without requiring a booted kernel lane.

# Driver Display Acceleration Boundary Design

Feature: FR-DRIVER-0011.

## Design

`DisplayAccelerationSummary` records backend kind, flush mode, cache policy,
DMA acceleration, and execute permission state.

- `framebuffer_mmio_summary` reports `framebuffer-mmio`, write-combining,
  dirty-rect flushing, non-DMA, and non-executable.
- `virtio_gpu_dma_summary` reports `virtio-gpu-dma`, coherent dirty-rect DMA,
  and non-executable mappings when initialized.
- `virtio_gpu_transfer_buffer_valid` accepts only valid page-aligned canonical
  shared DMA buffers with coherent or flush-required cache policy.

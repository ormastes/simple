# Driver Display Acceleration Boundary System Test Plan

Feature: FR-DRIVER-0011.

## Coverage

- BGA/framebuffer dirty rectangles are bounded and clear on flush.
- Framebuffer summary is `framebuffer-mmio`, write-combining, non-DMA, and
  non-executable.
- VirtIO-GPU summary is `virtio-gpu-dma` and DMA accelerated when available.
- VirtIO-GPU transfer buffers use valid canonical shared DMA descriptors.
- Backend selection prefers VirtIO-GPU DMA over framebuffer MMIO.

## Spec

- `test/system/driver_display_acceleration_boundary_spec.spl`

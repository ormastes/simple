# Driver Display Acceleration Boundary Architecture

Feature: FR-DRIVER-0011.

## Components

- `src/os/drivers/framebuffer/fb_driver.spl` owns framebuffer state, dirty
  rectangle tracking, and MMIO flush behavior.
- `src/os/drivers/virtio/virtio_gpu.spl` owns VirtIO-GPU device state and DMA
  transfer behavior.
- `src/os/drivers/gpu/display_boundary.spl` provides a small policy surface for
  display-service selection and SPipe coverage.

## Policy

Framebuffer MMIO is a CPU-mapped display path with write-combining and dirty
rectangles. VirtIO-GPU is the DMA-capable path and must use a valid
`SharedDmaBuffer` descriptor for transfer buffers. Capability summaries keep
those paths distinct so higher layers do not treat legacy framebuffer display as
DMA-capable.

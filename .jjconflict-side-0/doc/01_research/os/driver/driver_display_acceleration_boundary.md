# Driver Display Acceleration Boundary Local Research

Feature: FR-DRIVER-0011.

## Findings

- `FramebufferDriver` already tracks bounded dirty rectangles and clears them
  on present/flush.
- `FramebufferDriver.capabilities` distinguishes host buffers from
  `framebuffer-mmio`.
- `VirtioGpuDriver.capabilities` already reports `virtio-gpu-dma` when
  initialized.
- Shared DMA descriptors exist in `std.io.dma`, but display boundary policy was
  not represented as a small reusable model.

## Decision

Add an arithmetic/policy-only display boundary module that distinguishes legacy
framebuffer MMIO from VirtIO-GPU DMA and validates canonical shared DMA
transfer buffers.

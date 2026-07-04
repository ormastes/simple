# Driver Display Acceleration Boundary Requirements

Feature: FR-DRIVER-0011.

## Functional Requirements

- REQ-DRV-DISPLAY-001: Legacy framebuffer display must be represented as
  `framebuffer-mmio`, not as a DMA backend.
- REQ-DRV-DISPLAY-002: Framebuffer display summaries must document dirty-rect
  flushing, write-combining cache policy, and non-executable mappings.
- REQ-DRV-DISPLAY-003: VirtIO-GPU display summaries must advertise DMA only
  when the device is initialized.
- REQ-DRV-DISPLAY-004: VirtIO-GPU transfer buffers must satisfy the shared DMA
  descriptor contract.
- REQ-DRV-DISPLAY-005: Backend selection must prefer initialized VirtIO-GPU DMA
  and fall back to framebuffer MMIO otherwise.

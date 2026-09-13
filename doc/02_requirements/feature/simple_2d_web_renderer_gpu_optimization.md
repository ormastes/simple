<!-- codex-research -->
# Simple 2D and web renderer GPU optimization requirements

Selected: Feature Option A — evidence-first device-present pipeline.

## Functional requirements

- REQ-GPUUI-001: Build and validate the Chrome oracle library prerequisite
  before admitting Chrome/Simple differential or performance results.
- REQ-GPUUI-002: Separate production device-present from explicit
  capture/readback; steady display must not download the framebuffer.
- REQ-GPUUI-003: Own retained GPU buffers per surface and deterministically
  release or recreate them on resize, device loss, and shutdown.
- REQ-GPUUI-004: Expose real backend submission identities and fence/timeline
  completion through a bounded two-or-three-frame ring.
- REQ-GPUUI-005: Convert input/events into generation-checked scene deltas and
  damage; production async submission must not enqueue and immediately drain.
- REQ-GPUUI-006: Compact command traffic and provide device-native execution
  for hot emulated primitives without changing pixels or public APIs.
- REQ-GPUUI-007: Compare identical showcases for C Vulkan versus Simple Vulkan
  and Chrome versus Simple web only when both sides have compatible evidence.
- REQ-GPUUI-008: Preserve exact pixel behavior, event ordering, fallback
  honesty, and existing public rendering interfaces.

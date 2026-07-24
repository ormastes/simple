<!-- codex-research -->
# Engine2D Four-Backend Capture — Domain Research

## GPU readback

The Vulkan memory model distinguishes device-local and host-visible memory.
Readback therefore needs an explicit device-to-host transfer and completed
synchronization, not a CPU mirror labeled as Vulkan:
https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html

Metal's `getBytes` contract requires GPU writes to be complete before CPU
readback. Private textures must first be copied with a blit encoder to
CPU-accessible storage:
https://developer.apple.com/documentation/metal/mtltexture/getbytes(_:bytesperrow:from:mipmaplevel:)

## QEMU capture and events

QMP defines `screendump` and `input-send-event`. The latter supports key,
button, relative, and absolute pointer events, but QMP acceptance only proves
the host sent an event. Guest-side ordered receipts are still required:
https://www.qemu.org/docs/master/interop/qemu-qmp-ref.html

## ARM SIMD

AArch64 NEON provides vector integer operations suitable for pixel spans.
Execution evidence must come from the selected native path (for example,
immutable hit/chunk counters), not feature-name detection alone:
https://developer.arm.com/community/arm-community-blogs/b/operating-systems-blog/posts/arm-neon-programming-quick-reference

## Consequences

- Synchronize before hashing GPU pixels.
- Record the backend/device identity adjacent to the capture.
- Treat a QMP success response as injection evidence, not delivery evidence.
- Require SIMD execution counters and bit-exact scalar parity.
- Use a tolerant pixel comparison only for known rasterization differences;
  geometry, event sequence, dimensions, and source revision remain exact.

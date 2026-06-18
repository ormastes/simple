# Vulkan present() Host Readback Uses Per-Pixel Simple Loops (~134 s/frame) - 2026-06-18

## Severity
P2 (performance). `VulkanBackend.present()` takes ~134 seconds to bring a single
1280×720 frame back to host memory under the classic interpreter — the only mode
where real Vulkan is available. This makes displaying a Vulkan-rendered frame
unusable for interactive GUI regardless of how fast the GPU render is.

## Component
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
  - `me present()` (~line 622)
  - `_bytes_to_pixel_array(fb_bytes, w*h)` (byte → u32 conversion)
  - the trailing `while i < self.w * self.h: copy[i] = self.host_buf[i]` loop

## Summary
The device→host transfer itself is a bulk extern (`vulkan_sffi_read_buffer_bytes`,
fast). But the two follow-up steps are written as per-pixel Simple loops:
1. `_bytes_to_pixel_array` converts each 4-byte group into a `u32` (≈ 921,600
   iterations for 1280×720).
2. `present()` then copies `host_buf[i] → copy[i]` element-by-element (another
   ≈ 921,600 iterations).

Under the classic interpreter (~27k simple iterations/sec measured), ~1.8M
iterations ≈ **134 s** per `present()`. Measured directly:
```
present_1280x720_readback_us = 134653750   # 134.65 s for one frame
```

## Reproduce (classic interpreter, Vulkan-capable host)
```bash
SIMPLE_EXECUTION_MODE=interpret bin/simple run <bench.spl>
```
`VulkanBackend.create().init(1280,720)`, draw anything, then time one
`b.present()` with `rt_time_now_unix_micros()`.

## Root cause
Per-pixel host-side work expressed in Simple, executed by the interpreter. (This
path only runs in the classic interpreter because JIT/native stub `rt_vulkan_*`
to 0 devices — so the slow host loop cannot be escaped by switching to a faster
execution mode today.)

## Proposed fix
Move the byte→pixel materialization out of the interpreter:
- Add a bulk `rt_*` extern that reinterprets the framebuffer bytes directly into
  the `[u32]` host buffer (memcpy / endianness-correct reinterpret), replacing
  both `_bytes_to_pixel_array` and the element-by-element copy loop.
- Avoid the second copy entirely: have `present()` return / expose `host_buf`
  directly instead of duplicating it into `copy`.

Expected effect: present() readback drops from ~134 s to a single bulk copy
(sub-millisecond at memcpy bandwidth).

## Related
- Render-side throughput: `vulkan_per_primitive_submit_wait_throughput_2026-06-18`.
- Mode trap: `rt_vulkan_only_executes_under_classic_interpret_2026-06-17`.

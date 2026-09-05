# Vulkan device-dispatch primitives ignore the active stencil mask

- **ID:** `vulkan_device_dispatch_ignores_stencil_mask_2026-08-19`
- **Status:** PARTIALLY FIXED (2026-08-19) — `draw_rect_filled` routed through the
  masked host image path when a mask is active; the rest of the class is open.
- **Found:** 2026-08-19, via
  `test/02_integration/rendering/native_shader_backend_readback_matrix_spec.spl`
  (vulkan-vs-software masked-scene parity: 7 divergent pixels — Vulkan painted
  rect pixels where mask=0).

## Root cause

`VulkanBackend.set_mask` stores `mask_buf/mask_w/mask_h` host-side only. The
compute kernels (`pipe_rect_filled`, `pipe_line`, `pipe_circle_filled`,
`pipe_triangle`, `pipe_gradient`, `pipe_blit`) receive clip state via
`_pack_rect_pc`-style push constants but have **no mask plane**, so a device
dispatch paints straight through an active mask. Host-fallback paths
(`draw_image`, `draw_image_blend` host branch, `draw_gradient_rect_h` masked
branch) do honor the mask, which is why only device-dispatched ops diverge.

## Fixed so far

- `draw_rect_filled` (opaque): when `mask_buf.len() > 0`, builds a solid pixel
  run and delegates to `draw_image`, which applies clip AND mask
  (src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl). Alpha rects already
  went through `draw_image_blend`, whose native path rejects mask-active
  frames (`backend_vulkan.spl:~942`) and falls back to the masked host path.

## Still open (same class)

`draw_line`, `draw_circle`/`draw_circle_filled`, `draw_triangle_filled`,
`draw_gradient_rect` (vertical device kernel), and any other direct
`_dispatch_framebuffer_checked` op executed while a mask is active. Either
(a) add a mask storage-buffer binding to the kernels, or (b) gate every device
dispatch on `mask_buf.len() == 0` and take the masked host path, mirroring the
rect fix. Option (b) is mechanical and preserves parity; option (a) keeps the
GPU offload honest under masks.

## Reproduce

Masked-scene block of
`native_shader_backend_readback_matrix_spec.spl` (mask 4x4, rect+image), or any
`set_mask` + device-dispatched primitive compared pixel-for-pixel against the
software backend.

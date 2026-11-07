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

## 2026-11-07 remaining primitive routing repair

At release `68a6f89671421a65a1b99faba1b76cba592850eb`, rectangle
outlines, axis/diagonal lines, filled circles, filled triangles and vertical
gradients still reach mask-unaware framebuffer kernels. The common checked
dispatch helper has no mask plane or host-mask guard, and the line push
constants carry clip state only. This is a current source defect, independent
of whether a device is available on the audit host.

The source repair sends those five masked entrypoints through the existing
`backend_emu` rectangle, Bresenham, distance-test, barycentric and gradient
decompositions. Their filled-rectangle calls reach the already mask-aware
host image route. Unmasked branches retain the existing device code. Existing
completion-unknown guards remain before fallback, and negative masked circle
radii retain a named refusal rather than becoming the emulator's centre stamp.
The widened line-span refusal also precedes masked i32 emulation, so extreme
opposite endpoints cannot bypass it. The five shared decomposition functions
are explicitly public at their existing owner; this repair does not add new
imports of private helpers or change their bodies.
Circle outlines and rounded rectangles already use the shared decomposition;
clear retains its whole-surface semantics. No shader, descriptor, device lease,
mask layout or configured library family is replaced.

The existing device-free mask-plane spec is extended with independent 4x2
pixel oracles for all five entrypoints, both line routes, negative radius and
unknown-completion refusal, plus extreme x/y-span refusal before emulation.
It uses the existing asymmetric mask/backend setup
and checks the actual `image-copy-host-fallback` provenance. These are host
pixel/routing regressions, not invented GPU output or device evidence.

Verification status: authored source and tests only; runtime regressions and
Vulkan-versus-software device readback are UNRUN pending source review and
resource/platform admission. This does not mark the BugDB record fixed.

TODO(masked-shape-transfer): measure and batch the existing host fallback's
framebuffer transfers before making masked-frame performance claims. An
emulated primitive can issue one full-frame upload per decomposed span or
pixel; the correctness route therefore has a concrete O(frame pixels *
decomposed pieces) transfer cost. No 8K throughput, latency or GPU-only claim
follows from this repair. The fallback remains explicitly recorded as CPU work.

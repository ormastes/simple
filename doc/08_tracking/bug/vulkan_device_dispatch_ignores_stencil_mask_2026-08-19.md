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


### Arithmetic-domain repair after exact-PR review (2026-11-07)

The earlier helper-body-unchanged checkpoint was insufficient: masked routing
exposed i32 doubled-line-error overflow and inclusive triangle counters that
could increment past i32MAX. That source head is held, not admitted.

The revised shared line helper widens differences/error/doubled error to i64.
Axis lines stamp one run without a per-coordinate walk. The run owner widens
stroke growth and clips to framebuffer bounds before narrowing or allocating
the backend rectangle. Triangle edge functions use i64 with explicit x/y spans
<= i32MAX (2*i32MAX^2 < i64MAX), and compute the third edge directly instead
of subtracting two edge values from the determinant. Larger masked spans are
explicitly refused as `triangle-dispatch-size-invalid`, preserving pixels and
known completion. Triangle scan bounds are intersected with the framebuffer;
their counters are i64 and cannot wrap at an i32 endpoint. The shared helper
has the same domain check, without inventing a generic backend error channel.

Four additional device-free scenarios cover both large axis lines with literal
masked pixels, tiny x/yMAX triangles, a wide-product triangle with only eight
viewport samples, and out-of-domain refusal. All authored scenarios remain
UNRUN. No native/device/performance qualification or BugDB closure follows.


The same review also traced rectangle edge addition, circle squared radius,
and gradient channel-times-row overflow in the newly reachable helpers. The
coherent revision clips widened rectangle bounds before backend expansion,
scans only visible circle rows with an exact bounded i64 floor-square-root,
and interpolates gradient channels in i64 using each visible row's original
source offset. Three further authored literal-pixel cases cover maximum-width
outlines, i32MAX-radius circles, and the final two rows of a huge gradient.
These checks remain UNRUN and prior held source packets remain historical.


The follow-up review also rejected a billion-point near-axis CPU walk.
The revised line owner skips directly to the stroke-expanded viewport using
the original Bresenham phase: the dominant coordinate step k determines the
minor step as floor((k*minor_span+(major_span-1)/2)/major_span). This retains
strict half-tie rounding toward the starting minor coordinate, including
reversed endpoints, rather than restarting the recurrence at a clipped point.
Axis lines remain one clipped run. Non-axis masked host work is explicitly
limited to max(4096, framebuffer_width*framebuffer_height) centre steps per
call. An excessively thick stroke can expand the visible interval beyond that
budget; admission then records `line-host-work-budget-exceeded` before any
write, with completion state preserved. This is an explicit unsupported-work
domain, not partial drawing or invented successful rendering. The same shared
pure admission helper guards direct emulation calls. Near-axis and pre-write
refusal scenarios remain authored/UNRUN alongside the previous cases.

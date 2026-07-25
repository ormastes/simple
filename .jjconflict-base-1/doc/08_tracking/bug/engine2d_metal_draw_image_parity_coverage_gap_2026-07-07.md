# draw_image (kernel_blit_image) had a real Metal dispatch path but ZERO CPU-vs-Metal parity coverage

## Status
Closed (2026-07-07) — coverage gap, not a live divergence. No fix was needed;
reproduction proved CPU vs Metal already bit-exact for this op.

## Severity
Low (verification gap, not a rendering bug) — but worth tracking: a future
regression on either side (kernel or CPU oracle) would have shipped silently
undetected.

## Summary
Continuing the 2026-07-07 CPU-vs-Metal parity sweep (which landed the
`rounded_rect` fix — see
`engine2d_metal_rounded_rect_kernel_stale_outline_2026-07-07.md`), the sweep
enumerated every real Metal MSL kernel in
`src/lib/gc_async_mut/gpu/engine2d/backend_metal_msl.spl` (the dual-algorithm
surface where CPU and Metal implementations can independently diverge) against
what `engine2d_cpu_metal_parity_run.spl` / `engine2d_gpu_offload_evidence.spl`
actually exercise:

| kernel | parity coverage before this sweep |
|---|---|
| kernel_clear | yes (`clear`) |
| kernel_draw_line | yes (`line`) |
| kernel_draw_circle / kernel_draw_circle_filled | yes (`circle`, `circle_filled_blend`) |
| kernel_draw_gradient_rect | yes (`gradient`, `gradient_rect`) |
| kernel_draw_rect_filled / kernel_draw_rect_outline | yes (`rects`, `rect_blend`) |
| kernel_draw_rounded_rect / kernel_draw_rounded_rect_outline | yes (`rounded_rect`, `rounded_rect_outline`) |
| kernel_draw_triangle_filled | yes (`triangle`, `triangle_filled_blend`) |
| kernel_indexed_fill | yes (`indexed_fill`) |
| kernel_glyph_atlas_blit | yes (`text`, `text_edge`) |
| **kernel_blit_image** | **NO — zero coverage anywhere** |

`draw_image()` in `backend_metal.spl` has had a real GPU dispatch path since
the GPU-offload work landed (`self.mirror.draw_image(...)` always runs first
for the CPU-mirror readback fallback, then `if self.initialized and
self.d_framebuffer != 0 and self.session.pipe_blit != 0:` dispatches
`kernel_blit_image` and flips `gpu_frame_complete`) — but no `it`/scene ever
called `draw_image` on both a `CpuBackend`/`SoftwareBackend` and a
`MetalBackend` and compared the framebuffers. This is exactly the same class
of gap the `rounded_rect` bug was born from (a real dual-algorithm op with no
independent-implementation proof) — it just happened to not have gone wrong
yet.

## Reproduction (2026-07-07 sweep, before adding coverage)
Ad hoc probe (`CpuBackend` vs `MetalBackend`, `draw_image(4,4,8,8,...)` on a
32x32 surface): `IMAGE: MATCH mismatches=0/1024 gpu_ok=true`. Root cause of
"why it was already correct": `kernel_blit_image` (MSL) is a raw, unblended
`fb[dst_idx] = src[src_idx]` write with a `px/py` framebuffer-bounds clip —
and `SoftwareBackend.draw_image` (`backend_software.spl`) is the identical
"clip then raw copy, no blend" row loop. Both sides independently arrived at
the same trivial formula, so there was no divergence to fix.

## What this sweep added (ADDITIVE, no existing assertions touched)
- `backend_capability.spl`: `OP_DRAW_IMAGE = "draw_image"`, exported.
- `backend_metal.spl`: `capability()` now pushes `OP_DRAW_IMAGE` when
  `self.session.pipe_blit != 0` (same "device present AND pipeline actually
  compiled" honesty signal as `OP_DRAW_GRADIENT_RECT`/`OP_DRAW_ROUNDED_RECT`).
- `engine2d_cpu_metal_parity_run.spl`: new `image` scene — a fully
  on-surface blit, a right/bottom-edge-straddling blit, and a
  left/top-edge-straddling blit, all with a per-pixel-varied (non-solid)
  source buffer so a transposition/stride bug would show.
- `engine2d_gpu_offload_evidence.spl`: new `image` stage (`GPU_OFFLOAD_STAGE=image`),
  same scene shape, driven through `Engine2D.draw_image` with a
  `capability().is_accelerated("draw_image")` honesty check.
- `check-engine2d-gpu-offload-evidence.shs`: new `IMG_LINE`/`PROV_IMG` gate
  clauses requiring `MATCH` + `source=device_readback` on both the stage row
  and the provenance line — additive AND-terms, no existing clause weakened.
- `engine2d_shared_raster_parity_spec.spl`: new context "draw_image (blit)
  parity-sweep coverage close" — 4 `it` blocks pin an independent
  Simple-level replica of `kernel_blit_image`'s raw-copy-with-clip formula
  against `SoftwareBackend.draw_image` (on-surface, right/bottom clip,
  left/top clip, and fully-off-surface no-op).

## Verification
- `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`: new `image`
  row, `MATCH mismatches=0/1024 gpu_ok=true`; all 9 pre-existing scenes
  unchanged (`clear`/`rects`/`gradient`/`line`/`circle`/`rounded_rect`/
  `rounded_rect_outline`/`triangle`/`circle_filled_blend`/
  `triangle_filled_blend`/`degenerate_dims` all still `MATCH`); overall
  `PARITY: pass`, gate `pass (cpu-metal-bitexact)`.
- `scripts/check/check-engine2d-gpu-offload-evidence.shs`: new `image` row,
  `MATCH pixels=3072 source=device_readback`, real Metal checksums
  `cpu_checksum=1935043334 metal_checksum=1935043334` (equal), no
  `capability() under-report` WARN printed; full gate:
  `pass (cpu-metal-bitexact-device-readback)`.
- `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`:
  40 examples, 0 failures (was 36; +4 new `it` blocks, zero existing
  assertions edited — the 3 pre-existing intentionally-DIVERGENT rows
  `draw_line (thick)`/`draw_circle r<=0`/`draw_circle_filled r0` are
  unchanged, still correctly flagged).
- `scripts/check/check-ui-backend-isolation.shs`: `ui_backend_isolation_baselined=542
  ui_backend_isolation_current=542 ui_backend_isolation_new=0 ok=true`.
- `scripts/check/check-cpu-hotloop-idiom.shs`: `cpu_lane_hotloop_baselined=393
  cpu_lane_hotloop_current=393 cpu_lane_hotloop_new=0 ok=true`.

## Note on the rest of the dual-algorithm surface
This closes the last real MSL-kernel op that had zero parity coverage.
Combined with the pre-existing coverage (table above) and the 2026-07-07
`rounded_rect` fix, every `kernel_draw_*`/`kernel_blit_image`/
`kernel_indexed_fill`/`kernel_glyph_atlas_blit` in `backend_metal_msl.spl` is
now both dispatched-and-proven bit-exact against its CPU oracle. The many
other `draw_*` methods on `MetalBackend` (`draw_ellipse`, `draw_arc`,
`draw_bezier`, `draw_polygon_filled`, `draw_polyline`, `draw_rect_thick`,
`draw_circle_thick`, `draw_gradient_rect_h`, `draw_radial_gradient`,
`draw_rect_blend`, `draw_image_blend/scaled/transform`,
`draw_triangle_outline`, `draw_blur_rect`, `draw_shadow_rect`,
`draw_rect_blend_mode`) all delegate unconditionally to `self.mirror.<method>`
— they have no Metal kernel at all, so they are single-algorithm (not
dual-algorithm) and outside this parity class by construction; nothing to
prove there.

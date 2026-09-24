# rendering_buffer_preexisting_spec_failures_2026-10-03

Status: open
Date: 2026-10-03
Lane: Lane A (rendering buffer hardening, Simple 2D side)
Runtime note: all runs below are seed-run (diagnostic — not release-admissible),
Rust seed binary `bin/simple`, `--mode=interpreter`, in a shared dirty worktree
with parallel lanes actively editing the same files.

## What fails

Observed while verifying Lane A fixes; reproduced IDENTICALLY with Lane A's
hunks reverted, so none of these are caused by Lane A's changes (fixes:
`init_with_initial_color` in backend_software.spl/engine.spl, i64 dimension
guard in pixel_surface_content_frame.spl, preallocated crop buffer in
draw_ir_adv.spl `_engine2d_draw_ir_materialize_image_damage`).

1. `test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl`
   20/22 pass, 2 fail:
   - "packs disjoint source rows in supplied rectangle order"
   - "rejects overlapping or out-of-bounds requests without a partial payload"
   Both target `SoftwareBackend.read_damage_pixels_packed`
   (src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:1679). The packed
   transport or its spec expectations diverge from the damage plan contract.

2. `test/02_integration/rendering/engine2d_embedded_surface_spec.spl`
   6/10 pass, 4 fail (all Vulkan/Metal-session examples):
   - "opacity_milli=500 blends the embedded surface at ~50% over the background"
   - "composites a canonical offset translucent WM window on shared Vulkan and Metal sessions"
   - "uses the Vulkan device path only for preflighted root and named-child compositions"
   - "composites preflighted resolved text through checked Vulkan image blending"

3. `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl`
   66/69 pass, 3 fail:
   - "rejects strict retained damage when the mutable owner is not Vulkan"
   - "admits the canonical CSS background border overlay through fresh-device preflight"
   - "submits a GPU-selected Draw IR batch through the runtime host GPU queue"

4. `test/01_unit/lib/skia/raster_prims_spec.spl`
   12/13 pass, 1 fail:
   - "stroke_path of a line segment produces non-empty pixels"
   (`semantic: undefined field: unknown property, key, or method 'r' on
   Dict`). Reproduced with the 2026-10-03 W1 `Bitmap.zeros` hunk reverted,
   so it is not caused by that change; the stroke_path case appears to
   predate this lane.
   FIXED 2026-10-03: seed test-runner type-erasure defect, not a source
   bug — spec passes the color inline instead of a `val` binding. Root
   cause tracked in
   doc/08_tracking/bug/seed_val_bound_class_type_erasure_spec_context_2026-10-03.md.
   Spec now 13/13.

5. `test/01_unit/lib/skia/engine2d_bridge_spec.spl`
   15/16 pass, 1 fail:
   - "rejects rounded corners whose coverage ignores disabled antialiasing"
   Fails identically with the 2026-10-03 W3 `sk_image_to_u32_pixels` hunk
   present and with `engine2d_bridge.spl` at HEAD, so it is not caused by
   that change. Likely depends on parallel-lane rounded-rect coverage
   work outside this lane's edit surface.
   FIXED 2026-10-03: same seed type-erasure defect as item 4 (`'blend_mode'
   on Dict`) — spec passes the paint inline. See
   doc/08_tracking/bug/seed_val_bound_class_type_erasure_spec_context_2026-10-03.md.
   Spec now 16/16.

## Likely owner

The Vulkan/Metal-session and fresh-device/retained-damage failures coincide
with parallel-lane edits present in the shared worktree (vulkan affine
coverage, strict_vulkan_rect_clip, retained-damage paths). The
`read_damage_pixels_packed` pair is squarely Simple 2D buffer transport and
untracked as of this date.

## Reproduce

```
SIMPLE_LIB=src bin/simple test test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/simple test test/02_integration/rendering/engine2d_embedded_surface_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl --mode=interpreter
```

# Architecture: Simple 2D Completion (Engine2D & Skia CPU)

- **Date:** 2026-11-28
- **Status:** Active (`release/1.0.0`)
- **Requirements:** `doc/02_requirements/feature/simple_2d_completion.md` (`REQ-S2D-001..007`)
- **NFRs:** `doc/02_requirements/nfr/simple_2d_completion.md` (`NFR-S2D-001..006`)
- **Architecture Profile:** `mdsoc_plus` (`src/lib/gc_async_mut/gpu/engine2d`, `src/lib/skia`)

---

## 1. Architectural Decisions

### AD-1: Uniform Embedded-Surface Layering Rule Between CPU and Vulkan (`REQ-S2D-001`)
Previously `_engine2d_draw_ir_uses_embedded_surface` (`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:5285-5304`) set `needs_real_offscreen = true` whenever `backend == "vulkan"`, forcing opaque clipped WM windows (`opacity_milli == 1000`, `clip == true`) into a transparent (`da == 0`) offscreen layer on Vulkan while CPU drew directly onto the opaque parent (`da == 255`). Two sequential corner AA blends (`shrunk_rrect_background` + `hairline_rrect_border`) quantized differently in translucent intermediate space vs opaque parent space, causing a 1 LSB mismatch at 20 corner pixels.

**Decision:** Align Vulkan with CPU by removing `backend == "vulkan"` from `needs_real_offscreen` (`embedding.opacity_milli < 1000 or backend == "metal" or css_group`). Opaque clipped batches (`opacity_milli == 1000`, `clip == true`) execute directly on the parent under `set_clip(embedding.x, embedding.y, embedding.width, embedding.height)` on both CPU and Vulkan. Unfocused (`opacity_milli < 1000`), unclipped (`not embedding.clip`), and CSS opacity group batches remain layered on both backends.

### AD-2: Device-to-Device Layered Composite & Parent-Owned Offscreen Pool on Vulkan (`REQ-S2D-003`)
When an embedded batch requires a real offscreen surface on Vulkan (`opacity_milli < 1000` or unclipped), allocating a fresh `VulkanBackend`, reading pixels back to the host via `read_pixels_with_source()`, and re-uploading via `draw_ir_composite_readback` adds multi-second latency and violates the steady-state zero-readback contract (`rendering_ui/skill.md`).

**Decision:**
1. Add `Engine2D.draw_ir_composite_device_milli(layer, dst_x, dst_y, width, height, opacity_milli)` backed by `VulkanBackend.draw_image_layer_device(layer_buf, dst_x, dst_y, width, height, opacity_milli)`, using `vulkan_dispatch_region_kernel_checked(self.d_framebuffer, self.pipe_blit, layer_buf, pc, gx, gy, 1)` (respecting `self.clip_enabled` and `opacity_milli`, never transferring `layer_buf` ownership to the parent's free list).
2. Fall back cleanly to `layer.read_pixels_with_source()` + `eng.draw_ir_composite_readback(...)` only if device restore declines (e.g., mask active or host fallback).
3. Add parent-owned pooled offscreen buffer reuse on `VulkanBackend` (`reusable_offscreen_fb`, `reusable_offscreen_w`, `reusable_offscreen_h`), freed deterministically in `VulkanBackend.shutdown()` so `VulkanSession.ref_count` is never leaked even when callers invoke `engine.shutdown()` on the initial `Engine2D` handle.

### AD-3: Consistent `opacity_milli < 1000` Admission Across Retained Damage Paths (`REQ-S2D-002`, `REQ-S2D-004`)
Unify `engine2d_draw_ir_prepare_damage_plan` and `engine2d_draw_ir_render_composition_damaged` (`draw_ir_adv.spl`) with `_engine2d_draw_ir_render_composition_damaged_with_images`:
- Valid embeddings require `width > 0`, `height > 0`, `0 < opacity_milli <= 1000`, `not _engine2d_draw_ir_batch_samples_parent(batch)`, and whenever `opacity_milli < 1000`, a non-empty `surface_id` (plus non-CSS-group / non-Metal target for retained replay).
- Anonymous translucent batches (`surface_id == ""` with `opacity_milli < 1000`), invalid opacity (`<= 0` or `> 1000`), and parent-sampling batches continue to fail closed with `"retained-composition-unsafe-embedding"` in the generic composition paths.
- `engine2d_draw_ir_render_prepared_damage_plan_with_images` groups entries for layered batches (`_engine2d_draw_ir_retained_layer_batch`) or delegates to the layered offscreen composite path when any batch has `opacity_milli < 1000`, preserving `clip` and `opacity_milli`.
- Parent-sampling (`fluid_light` / `aetheric_dark`) retained damage replay (`src/os/compositor/engine2d_wm_frame_executor.spl`) routes non-parent backdrops and parent-sampling glass overlays through checked device offscreen + region read/patch when on Vulkan.

### AD-4: Real Offscreen `SaveLayer` Stack & Full-Mode Coverage Blending in Skia CPU (`REQ-S2D-005`, `REQ-S2D-006`)
Inline propagation of `SaveLayer`'s `blend_mode` onto child draws corrupts intra-layer overlaps and skips layer isolation.

**Decision:**
1. Extend `CanvasState` (`src/lib/skia/backend/cpu/backend.spl`) with `target: Bitmap`, `is_layer: bool`, `layer_alpha: f64`, `layer_mode: SkBlendMode`, and `layer_clip: SkRect`.
2. `SaveLayer` allocates an isolated transparent premultiplied `Bitmap`, pushes a layer state (`alpha: 1.0`) so child draws blend only against each other using each child's own `op.paint.blend_mode`, and `Restore` composites the layer onto the parent `Bitmap` once over `layer_clip` using `layer_alpha` and `layer_mode`.
3. Provide one shared coverage-weighted pixel compositing helper `_blend_bitmap_pixel(bitmap, x, y, src_straight, mode, cov)` that:
   - Unpremultiplies `dst` from `Bitmap` when needed for W3C separable/HSL modes (`hsl.spl`),
   - Routes `SkBlendMode.Screen` through W3C alpha-aware `hsl.blend_screen` (matching Skia/Chrome `porter_duff_golden.spl`),
   - Interpolates `lerp(dst_premul, compose(src, dst, mode), cov)` for fractional AA coverage `cov in [0, 1]`.
4. Route `DrawRect` (axis-aligned & transformed), `DrawRRect`, `DrawOval`, `DrawPath`, `DrawImage` (reading real `dst` from `cur.target` instead of `(0,0,0,0)`), and `DrawPaint` through this unified blend path.

### AD-5: Lossless Full 3x3 Affine Matrix Encoding in `SkPictureOp` (`REQ-S2D-007`)
Adding a required field to `class SkPictureOp` would break ~25 existing `SkPictureOp(...)` struct literals across unit, integration, and system specs.

**Decision:** Mirror the existing `sk_pack_text_blob_op_image` pattern (`src/lib/skia/entity/textblob.spl`) using a pure value representation on `SetMatrix`: `_canvas_record_set_matrix` (`src/lib/skia/entity/canvas.spl`) continues filling `(rect, rx, ry)` for legacy callers AND attaches `path: Some(sk_pack_matrix_op_path(m))` encoding `(m00, m01)`, `(m02, m10)`, `(m11, m12)` in exact `f64` `SkPath` vertices. `CpuBackend` decodes `sk_unpack_matrix_from_path(op.path)` first and falls back to `(rect, rx, ry)` when `op.path` is `None`.

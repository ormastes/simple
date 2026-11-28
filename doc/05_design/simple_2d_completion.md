# Detail Design: Simple 2D Completion (Engine2D & Skia CPU)

- **Date:** 2026-11-28
- **Status:** Active (`release/1.0.0`)
- **Architecture:** `doc/04_architecture/simple_2d_completion.md`

---

## 1. Slice 1 — Engine2D GPU/Damage & Corner AA Parity (`REQ-S2D-001..004`)

### 1.1 Focused Window Corner AA & Uniform Embedded Rule (`REQ-S2D-001`)
- **File:** `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`
- **Symbol:** `_engine2d_draw_ir_uses_embedded_surface(batch, eng, depth)` (L5285-5304)
- **Change:**
  ```simple
  val needs_real_offscreen = (embedding.opacity_milli < 1000 or
      backend == "metal" or css_group)
  ```
  Removing `backend == "vulkan"` makes Vulkan and CPU select the exact same direct clipped path when `embedding.opacity_milli == 1000` and `embedding.clip == true`.
- **Verification spec:** `test/02_integration/rendering/engine2d_focused_window_corner_device_spec.spl` (remove `# @tag:in-development`).

### 1.2 Vulkan Pooled Shared Offscreen & Device-to-Device Layer Composite (`REQ-S2D-003`)
- **File:** `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
  - Add fields on `VulkanBackend` (initialized to `0` in `create()`):
    - `embed_scratch_fb: i64`
    - `embed_scratch_w: i32`
    - `embed_scratch_h: i32`
  - Add helper `me acquire_embed_scratch_fb(w: i32, h: i32) -> i64`:
    - If `self.embed_scratch_fb > 0 and self.embed_scratch_w == w and self.embed_scratch_h == h`: reuse `self.embed_scratch_fb`.
    - Otherwise free old `self.embed_scratch_fb` if `> 0`, allocate `w * h * 4` via `vulkan_sffi_alloc_buffer(byte_size, 0x80)`, store dimensions, return handle.
  - Free `self.embed_scratch_fb` cleanly inside `VulkanBackend.shutdown()` before `self.session.release()`.
  - Add `me draw_image_layer_device(layer_buf: i64, dst_x: i32, dst_y: i32, w: i32, h: i32, opacity_milli: i32) -> bool`:
    - Validate `not self.completion_unknown`, `self.initialized`, `self.d_framebuffer > 0`, `layer_buf > 0`, `self.pipe_blit > 0`, `not self.cpu_fallback_used`, `not self.cpu_fallback_host_surface`, `self.mask_buf.len() == 0`, `w > 0`, `h > 0`, `0 < opacity_milli <= 1000`.
    - If `self.clip_enabled and (self.clip_w <= 0 or self.clip_h <= 0)`: return `true` (clipped empty).
    - Flush pending compute on `self` (`self._flush_pending_compute_at("embed-layer-device")`); if `< 0`, set `completion_unknown = true` and return `false`.
    - Pack `_pack_image_composite_pc(dst_x, dst_y, w, h, self.w, self.h, self.clip_x, self.clip_y, self.clip_w, self.clip_h, self.clip_enabled, opacity_milli, VK_IMAGE_COMPOSITE_SRC_OVER, w, h)`.
    - Dispatch `vulkan_dispatch_region_kernel_checked(self.d_framebuffer, self.pipe_blit, layer_buf, pc, (w + 15) / 16, (h + 15) / 16, 1)`.
    - Update `dirty`, `host_mirror_frame_fresh = false`, `hint_damage(dst_x, dst_y, w, h)`, `consume_damage_hint()`, `mark_device_content_changed()`.
- **File:** `src/lib/gc_async_mut/gpu/engine2d/engine.spl`
  - Add `me acquire_shared_vulkan_offscreen_pooled(width: i32, height: i32) -> Result<Engine2D, text>` and `me release_shared_vulkan_offscreen_pooled(layer: Engine2D)` (reuses `parent.embed_scratch_fb` without creating/freeing a device buffer per replay, and clears `d_framebuffer = 0` on the temporary `VulkanBackend` wrapper before calling `session.release()` so `parent` retains ownership of `embed_scratch_fb` and frees it on `parent.shutdown()`).
  - Add `me draw_ir_composite_device_milli(layer: Engine2D, dst_x: i32, dst_y: i32, width: i32, height: i32, opacity_milli: i32) -> bool`: flushes `lvk._flush_pending_compute_at("milli-layer")`, calls `vk.draw_image_layer_device(lvk.d_framebuffer, dst_x, dst_y, width, height, opacity_milli)`, updates `self.vulkan_backend` / `self.backend`.
- **File:** `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`
  - In `_engine2d_draw_ir_render_batch_embedded` and `_engine2d_draw_ir_render_composition_damaged_with_images`:
    - On Vulkan, acquire via `eng.acquire_shared_vulkan_offscreen_pooled(embedding.width, embedding.height)` (falling back to `draw_ir_create_offscreen_engine` if unavailable).
    - When `not css_group` and `eng.backend_name() == "vulkan"`, attempt `eng.draw_ir_composite_device_milli(layer, embedding.x, embedding.y, embedding.width, embedding.height, embedding.opacity_milli)` first (for each clip in replay, or whole embedding in full-frame), falling back to `layer.read_pixels_with_source()` + `eng.draw_ir_composite_readback(...)` only if device composite declines.
    - Release pooled Vulkan layer via `eng.release_shared_vulkan_offscreen_pooled(layer)`.

### 1.3 Prepared Damage Plan & Single-Root Admission for `opacity_milli < 1000` (`REQ-S2D-002`)
- **File:** `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`
- **Helper:** `_engine2d_draw_ir_retained_embedding_safe(batch: DrawIrBatch) -> bool`:
  - Returns `true` iff `embedding.width > 0`, `embedding.height > 0`, `embedding.opacity_milli > 0`, `embedding.opacity_milli <= 1000`, `(embedding.opacity_milli == 1000 or embedding.surface_id != "")`, and `not _engine2d_draw_ir_batch_samples_parent(batch)`.
- **Prepared damage plan (`engine2d_draw_ir_prepare_damage_plan` & `_engine2d_draw_ir_render_prepared_damage_plan_with_images`):**
  - Replace `embedding.opacity_milli != 1000` rejection with `not _engine2d_draw_ir_retained_embedding_safe(batch)`.
  - In `_engine2d_draw_ir_render_prepared_damage_plan_with_images`, if any batch in `prepared.composition.batches` requires `_engine2d_draw_ir_retained_layer_batch(batch, eng)` (e.g. `opacity_milli < 1000`), ensure `eng` rejects if `embedding.opacity_milli < 1000 and (eng.backend_name() == "metal" or css_opacity_group_surface(embedding.surface_id))` with `"retained-composition-unsafe-embedding"`, and render layered batches via the exact same batch-major offscreen-and-composite loop used in `_engine2d_draw_ir_render_composition_damaged_with_images` (using `prepared` damage rects / entries).
- **Single-root fast path (`engine2d_draw_ir_render_composition_damaged`):**
  - Replace `embedding.opacity_milli != 1000` with `not _engine2d_draw_ir_retained_embedding_safe(batch)`.
  - When `embedding.opacity_milli < 1000` (or offset/cropped), delegate to `_engine2d_draw_ir_render_composition_damaged_with_images(engine, composition, images, damage_rects, readback_frame, false)`.

### 1.4 Parent-Sampling Retained Damage Replay (`REQ-S2D-004`)
- **File:** `src/os/compositor/engine2d_wm_frame_executor.spl`
  - Inspect `_wm_replay_parent_sampling_composition` (L335-485): already implemented for `fluid_light`/`aetheric_dark` with Vulkan `stage_present_damage` and `device_readback` patch guard; verify against `engine2d_wm_local_lane_clock_tick_spec.spl` and ensure `scratch` reuses pooled Vulkan offscreen when available / handles `read_pixels_region` cleanly without whole-surface downloads.

---

## 2. Slice 2 — Skia CPU `SaveLayer`, Blend Modes & Full 3x3 Affine Matrices (`REQ-S2D-005..007`)

### 2.1 Lossless Full 3x3 Matrix Packing (`REQ-S2D-007`)
- **File:** `src/lib/skia/entity/canvas.spl`
  - Add `sk_pack_matrix_op_path(m: Matrix3x3) -> SkPath` and `sk_unpack_matrix_from_path(path_opt: Option<SkPath>) -> Option<Matrix3x3>` (encoded as `Move(m00, m01)`, `Line(m02, m10)`, `Line(m11, m12)` with exact `SkPathFillType.Winding`, identifiable by exactly 3 segments `[Move, Line, Line]`).
  - Update `_canvas_record_set_matrix` (L79-100) to set `path: Some(sk_pack_matrix_op_path(m))` while retaining `rect`, `rx`, `ry` for backward compatibility.
- **File:** `src/lib/skia/backend/cpu/backend.spl`
  - In `SetMatrix` replay (L257-286): check `sk_unpack_matrix_from_path(op.path)` first; if `Some(mat)`, use `mat` directly (`m20=0, m21=0, m22=1`); otherwise use the legacy `(op.rect, op.rx, op.ry)` decoder.
  - Remove duplicate `val color = _scale_alpha(_paint_color4f(op.paint), cur.alpha)` at L307.

### 2.2 W3C Alpha-Aware `Screen` & Unified Coverage-Weighted Compositor (`REQ-S2D-006`)
- **File:** `src/lib/skia/feature/blend/blend_compose.spl` & `porter_duff.spl`
  - Route `SkBlendMode.Screen` in `blend_compose.spl` to `hsl.blend_screen` (`_sep(sc, dc, sa, da, sc + dc - sc*dc)`), which handles `src.a < 1.0` per W3C/Skia (`porter_duff_golden.spl` `[40, 200] == [121, 164, 248, 255]`) while remaining identical to `porter_duff.blend_screen` when `sa == 1.0` or `sa == 0.0` (`blend_spec.spl`).
- **File:** `src/lib/skia/backend/cpu/backend.spl`
  - Add `_unpremul_dst(bitmap: Bitmap, x: i64, y: i64) -> (SkColor4f, SkColor4f)` returning `(dst_premul, dst_straight)`.
  - Add `_compose_onto_premul(src_straight: SkColor4f, dst_premul: SkColor4f, dst_straight: SkColor4f, mode: SkBlendMode) -> SkColor4f`:
    - For `SrcOver`: `blend_src_over(src_straight, dst_premul)`.
    - For Porter-Duff modes (`Clear`, `Src`, `Dst`, `DstOver`, `SrcIn`, `DstIn`, `SrcOut`, `DstOut`, `SrcATop`, `DstATop`, `Xor`, `Plus`, `Modulate`): convert `src_straight` to premultiplied `src_pm = (r*a, g*a, b*a, a)` and apply the exact Porter-Duff premultiplied equations over `dst_premul`.
    - For separable/HSL modes (`Screen`, `Overlay`, `Darken`, `Lighten`, `ColorDodge`, `ColorBurn`, `HardLight`, `SoftLight`, `Difference`, `Exclusion`, `Multiply`, `Hue`, `Saturation`, `Color`, `Luminosity`): call `apply_blend(src_straight, dst_straight, mode)` (which produces premultiplied output via `_sep`).
  - Add `_blend_bitmap_pixel_mode(bitmap: Bitmap, x: i64, y: i64, src_straight: SkColor4f, mode: SkBlendMode, cov: f64)`:
    - Early out if `cov <= 0.0` or `(x, y)` out of bounds.
    - If `mode == SkBlendMode.SrcOver`: delegate directly to `bitmap.blend_pixel(x, y, src_straight, cov)`.
    - Otherwise compute `composed = _compose_onto_premul(src_straight, dst_premul, dst_straight, mode)` and store `dst_premul * (1.0 - cov) + composed * cov` clamped to `[0, 255]`.
  - Add `_blend_bitmap_diff(base_bm: Bitmap, layer_bm: Bitmap, mode: SkBlendMode, clip: SkRect, color: SkColor4f)` or pass `mode` through AA rect/rrect/path/image/paint/text rasterization:
    - For `DrawRect` (axis-aligned & transformed), `DrawRRect`, `DrawOval`, `DrawPath`, `DrawPaint`:
      - When `mode == SkBlendMode.SrcOver`, keep fast existing `fill_rect` / `fill_rrect` / `fill_path_aa` / `stroke_path` unchanged.
      - When `mode != SkBlendMode.SrcOver`:
        - Axis-aligned `DrawRect`: analytic x/y pixel coverage (`fill_rect` edge math) calling `_blend_bitmap_pixel_mode(..., mode, cov)` (fixes missing edge AA in old `_fill_rect_mode` AND respects `cur.clip`!).
        - Transformed `DrawRect`: `_fill_transformed_rect` calls `_blend_bitmap_pixel_mode(..., mode, cov)`.
        - `DrawRRect` / `DrawOval` / `DrawPath` (Fill & Stroke): render shape coverage into a tight scratch `Bitmap` (opaque white `1,1,1,1` coverage mask) via existing `fill_rrect` / `fill_path_aa` / `stroke_path`, then composite touched pixels onto `cur.target` with `_blend_bitmap_pixel_mode(..., color, mode, cov)` (bounded by `cur.clip`). Zero duplicated path/AA math!
        - `DrawPaint`: loops over `cur.clip` calling `_blend_bitmap_pixel_mode(..., color, mode, 1.0)`.
    - For `DrawImage` (identity & transformed): read actual destination pixel from `cur.target` at `(dst_x, dst_y)` / `(px, py)` and call `_blend_bitmap_pixel_mode(cur.target, ..., sampled, op.paint.blend_mode, cur.alpha)`.

### 2.3 Real Offscreen `SaveLayer` & `Restore` Isolation (`REQ-S2D-005`)
- **File:** `src/lib/skia/backend/cpu/backend.spl`
  - Extend `CanvasState`:
    ```simple
    class CanvasState:
        alpha: f64
        clip: SkRect
        transform: Matrix3x3
        target: Bitmap
        is_layer: bool
        layer_alpha: f64
        layer_mode: SkBlendMode
        layer_clip: SkRect
    ```
  - `Save`: pushes cloned state sharing `top.target`, `is_layer: false`.
  - `SaveLayer`:
    - Computes `layer_clip = intersect_rect(top.clip, _transformed_rect_bounds(op.rect, top.transform))` (or `top.clip` when `op.rect` is empty).
    - Allocates `layer_bm = Bitmap.zeros(safe_w, safe_h)`.
    - Pushes `CanvasState(alpha: 1.0, clip: layer_clip, transform: top.transform, target: layer_bm, is_layer: true, layer_alpha: layer_color.a, layer_mode: op.paint.blend_mode, layer_clip: layer_clip)`.
  - `Restore`:
    - Pops `popped` when `stack_depth > 1`.
    - If `popped.is_layer`: iterates `y` in `[floor(layer_clip.top)..ceil(layer_clip.bottom))` and `x` in `[floor(layer_clip.left)..ceil(layer_clip.right))` clamped to `[0..safe_w, 0..safe_h)`, reads premultiplied `popped.target` pixel `(x, y)`, skips if `a == 0`, scales by `popped.layer_alpha`, unpremultiplies to `src_straight` with effective alpha `la * popped.layer_alpha`, and calls `_blend_bitmap_pixel_mode(parent.target, x, y, src_straight, popped.layer_mode, 1.0)`.
  - Update all draw ops in `render_picture` to target `cur.target` instead of `bitmap`, and return `state_stack[0].target` at the end of `render_picture`.

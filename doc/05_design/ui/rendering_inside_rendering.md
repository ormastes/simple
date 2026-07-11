# Detail Design: Rendering Inside Rendering

Architecture: `doc/04_architecture/ui/rendering_inside_rendering.md`

## 2D — embedded render target (landed)
File: `src/lib/gc_async_mut/gpu/engine2d/engine.spl`
- `fn Engine2D.create_offscreen(w: i32, h: i32) -> Engine2D` — forces the
  CPU/software backend; clears to `0x00000000` (fully transparent) so
  uncovered pixels let the parent show through on composite.
- `me draw_engine(dst_x: i32, dst_y: i32, src: Engine2D)` —
  `draw_image_blend(dst_x, dst_y, src.width(), src.height(), src.read_pixels())`.
- `me draw_engine_opacity(dst_x, dst_y, src, opacity_milli: i32)` — scales
  source alpha by `opacity_milli/1000` (helper `engine2d_scale_pixel_alpha`)
  before the blend.

File: `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`
- `_engine2d_draw_ir_render_commands(...)` — shared command loop extracted
  from the batch/composition paths.
- `_engine2d_draw_ir_render_batch_embedded(...)` — for a batch whose
  `embedding.surface_id != ""`: render commands relative to the embedded
  origin into `create_offscreen(embedding.width, embedding.height)`, then
  composite at `(embedding.x, embedding.y)` with `opacity_milli`.
  `ENGINE2D_DRAW_IR_EMBED_MAX_DEPTH = 3`; past the cap, legacy translate+clip.
- Perf guard: embedding at `(0,0)` with full opacity and exactly the target
  size skips the offscreen round-trip (provably 1:1). Prevents double-buffer
  cost on the WM desktop root batch (`widget-root`).
- Behavior note: WM window batches already set `surface_id`, so
  `opacity_milli` (e.g. 930 on unfocused windows) is now honored — previously
  carried-but-ignored schema metadata activated by design.

Spec: `test/02_integration/rendering/engine2d_embedded_surface_spec.spl`
(offset composite + transparency, IR surface clipping, 500-milli blend math,
depth-2 nesting, no-`surface_id` regression guard).

## Web — iframe-like embedding (Lane B, landed)
File: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- Parse: `iframe` becomes a replaced element; inner content never lays out in
  the parent. Attributes: `srcdoc` (primary), `src` (local file only),
  `width`/`height` (default 300x150), `space` = `separate` (default) |
  `shared`.
- Paint: recursive render of the child document to an offscreen `[u32]`
  buffer at the iframe content size; blit at box origin, clipped. Depth cap 3
  (placeholder fill beyond); child receives a fraction of remaining
  `budget_ms`.
- `space=shared`: parent CSS rules also apply to the child (child overrides);
  `separate`: child sees only its own styles.

Spec: `test/02_integration/rendering/simple_web_iframe_embedding_spec.spl`.

## GUI/WM — nested content frames (Lane C, landed)
File: `src/lib/common/ui/window_scene.spl`
- `WmContentFrame` += `parent_window_id: text` (empty = top-level),
  `offset_x: i32`, `offset_y: i32` (relative to parent content rect).
- `WM_CONTENT_ORIGIN_GUI = "gui"` added next to `simple_web`.

File: `src/lib/common/ui/window_scene_draw_ir.spl`
- `_shared_wm_content_frame_for_window` accepts origins {simple_web, gui};
  validation (revision/checksum/size) unchanged and fail-closed.
- `_shared_wm_scene_render_context_content_to_backend`: after the top-level
  blit, recursively blit child frames at
  `(content.x + offset_x, content.y + offset_y)`, offsets accumulating,
  cropped to the parent content rect via a pure crop helper (no
  `CompositorBackend` change), depth cap 3. Invalid child → magenta child
  rect only.
- Child batches set `DrawIrEmbeddingConfig.surface_id` = child window id and
  `DrawIrCommand.parent_id` = parent window id in the Draw IR projection.

File: `src/os/compositor/simple_web_window_renderer.spl`
- `simple_web_child_content_frame_cached(...)` — web frame stamped with
  parent/offset, sharing the existing render internals.
- `wm_gui_content_frame_from_pixels(...)` — GUI-origin frame from raw pixels
  using the same checksum function as web frames.

Spec: `test/02_integration/rendering/wm_nested_content_frame_spec.spl`.

## 3D — node nesting (Lane D, landed)
File: `src/app/model3d/main.spl`
- `Node3.children: [Node3]` (child `center` relative to parent); recursive
  raster traversal, depth cap 8; `Scene3.embed(parent_name, child) -> bool`.

Spec: `test/02_integration/app/model3d/model3d_nested_nodes_spec.spl`.

## Final verification
Browser chrome (buttons, GUI widgets, text fields) rendered through the
embedding paths with pixel assertions; evidence script follows the
fail-closed `scripts/check/check-*-evidence.shs` pattern.

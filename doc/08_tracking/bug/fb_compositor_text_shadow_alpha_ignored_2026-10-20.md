# draw_text_shadow alpha is not applied on the framebuffer path

- `src/os/compositor/text_render.draw_text_shadow` stores the shadow colour with
  its alpha channel replaced by `shadow_alpha`, via `draw_text_scaled`'s raw
  pixel write. `FbCompositorBackend` / framebuffer buffers store ARGB without
  compositing, so the shadow renders as an opaque colour.
- Fix needs a read-modify-write blend against the existing pixel (backend
  `read_pixel` / `blend_rect` via `CompositorGlassCapable`); not trivial because
  `draw_text_scaled` has no per-pixel blend path.
- Also: `FbCompositorBackend.draw_text` truncates non-ASCII characters to the
  low byte (8x16 bitmap font is ASCII only).

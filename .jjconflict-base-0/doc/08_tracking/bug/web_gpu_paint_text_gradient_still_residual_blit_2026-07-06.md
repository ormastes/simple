# web GPU-paint: text / gradient / border still fall to residual CPU-blit

- **status:** open (follow-up to the landed rect offload)
- **severity:** medium (correctness is fine — parity is bit-exact; this is an
  offload-coverage gap, not a rendering bug)
- **area:** lib / gpu / browser_engine (web render lane)
- **date:** 2026-07-06

## Context

`SIMPLE_WEB_GPU_PAINT=1` now composes the web frame from REAL per-primitive
Engine2D backend calls: one `draw_rect_filled` per solid opaque border-box CSS
box, plus a single residual blit of whatever the fills did not reproduce.
Verified bit-exact on `css_boxes.html` @320x240 (rect=4, gradient=0, blit=0,
`gpu_backend_used=true`, `device_readback`) — see
`test/02_integration/rendering/web_gpu_paint_parity_run.spl`.

The residual is measured against the ACTUAL Metal readback and blitted from the
CPU ground truth, so parity holds by construction for ANY page. The gap is that
non-solid-rect primitives are NOT yet emitted as their own GPU ops — they land
in the residual dirty rect and are uploaded/blitted as one CPU sub-image. On a
text- or gradient-heavy page that residual can cover most of the frame, so the
offload win shrinks toward the old upload-bound behavior for those pages.

## What is still residual (not yet a real per-primitive GPU op)

Emitter that currently skips them:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
`_web_gpu_solid_fill_ops` (the `plain_solid` predicate skips all of these).

1. **Text / glyphs.** CPU path rasterizes a 5x7 bitmap font glyph-by-glyph:
   - `fb_glyph_thin_scaled_clip` (renderer line ~6186) writes individual pixels
   - `fb_text_thin_scaled_clip_range` (line ~6214), widget variant
     `fb_text_sparse_range` (line ~6279)
   - paint text pass call sites lines ~8238-8322 (`fb_text_*` at 8287/8288/8313/8314)
   To offload: emit per-run glyph-quad ops (string + baseline x/y + color +
   advance + scale) and add a Metal glyph kernel that matches the 5x7 raster
   EXACTLY, OR emit each text run's bbox as an `image` op (small CPU sub-image
   blit) instead of folding it into one big residual — the latter keeps it on
   CPU pixels but makes it a genuine per-primitive blit.

2. **Gradients.** CPU path decomposes into per-row spans with
   `mix_color_vertical_centered` (renderer lines ~5918/5922) inside
   `fb_style_background_opacity_clip` (line ~5850, gradient branch guarded at
   line ~5892). `SceneCommand`/`Engine2D` already have `gradient_rect` +
   `kernel_draw_gradient_rect`; before emitting a `gradient_rect` op the MSL
   integer-lerp must be proven bit-exact vs `mix_color_vertical_centered`
   (float->int rounding). Until then it stays residual.

3. **Borders, rounded-rect backgrounds, box-shadows, `<img>` placeholders.**
   Skipped by `plain_solid` (`no_radius` / border-box-clip / alpha==255 gates).
   `stroke_rect` / `rounded_rect` ops + kernels exist; each needs a bit-exact
   parity check before being emitted.

## Consumer

`present_gpu_paint_readback` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl`
dispatches `frame.fill_ops` then patches the residual. Adding a new op kind = 
extend `_web_gpu_solid_fill_ops` to emit it AND dispatch it in
`present_gpu_paint_readback` (reuse the existing `SceneCommand` vocabulary and
`engine2d_executor`-style dispatch — do NOT add a parallel display-list type).

## Acceptance

For a text+gradient fixture through `SIMPLE_WEB_GPU_PAINT=1` on Metal:
`gradient=M>0`, per-run text ops dispatched, residual `blit_pixels` near zero,
and `gpu_vs_cpu_oracle_mism=0` still holds.

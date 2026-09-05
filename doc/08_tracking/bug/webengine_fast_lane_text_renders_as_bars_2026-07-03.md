# Bug: web-engine fast Metal lane renders text runs as solid bars, not glyphs

- **Date:** 2026-07-03
- **Severity:** medium (web-engine WM phase visually proves layout but text is unreadable)
- **Area:** Draw IR text command execution in Engine2D gpu-only fast mode
- **Status:** RESOLVED 2026-07-03

## Symptom
In the WM demo web-engine phase (html -> layout -> draw ir -> fast metal ->
present), text elements (window titles, content lines) appear as solid black
bars in the presented frame and in fullscreen_webengine.png. Rects, colors,
and layout geometry are correct (titlebar blue band check passes).

## Cause (suspected)
The Draw IR text command in the gpu-only fast lane is executed as a filled
rect (or the glyph path is skipped when the 1x1 mirror can't rasterize),
instead of routing to the existing GPU glyph path
(MetalBackend.draw_text_hires / kernel_blit_image, proven in the fit phase).

## Expected
Draw IR text commands in fast mode should rasterize glyphs via the existing
hi-res GPU text path (or CPU-glyph blit upload) so web-engine-rendered WM
text is readable.

## Evidence
build/wm_fullscreen_metal_evidence/fullscreen_webengine.png (2026-07-03
08:37 run, gate exit 0, webengine_capture_blue=ok).

## Root cause (confirmed by probe)
The HTML layout renderer never carried the text glyphs into the Draw IR at all.
`_html_draw_ir_command` (simple_web_html_layout_renderer.spl) emitted every node
-- including `#text` nodes -- as `draw_ir_box_with_style` (kind = RECT) with
`color = st.bg`. A `#text` node's background is transparent, so the command's
color was `0x00000000`. The Draw IR executor's RECT branch
(engine2d_draw_ir_adv_composition / _batch) called
`engine.draw_rect_filled(x, y, w, h, 0)`, and the Metal `kernel_rect_filled`
kernel stores the raw color word (no alpha blend). Storing `0x00000000` over the
parent's opaque white div fill left a fully-zero (transparent-black) rectangle
covering the whole text-run bounding box, which reads back / encodes as a solid
black bar. The actual glyphs were never drawn because no `DRAW_IR_COMMAND_TEXT`
command (and no `text_value`) was ever produced. Probe of the raw IR for
`<div ...>HELLO WORLD</div>`: `kind=rect id=text_4 ... color=0 txt=''`.

## Fix
1. `common/ui/draw_ir.spl` -- new `draw_ir_text_styled(...)` builder producing a
   `DRAW_IR_COMMAND_TEXT` command that carries the node's `computed_style` (so
   the executor can recover the pixel `font-size`).
2. `simple_web_html_layout_renderer.spl` -- `_html_draw_ir_command` now emits a
   text command (content position, `st.fg` color, computed style) for `#text`
   nodes with content instead of a transparent box.
3. `engine2d/draw_ir_adv.spl` (both batch and composition loops):
   - RECT branch skips fully transparent fills (alpha == 0) -- a no-op paint in a
     real compositor, so no more zero-color bars.
   - TEXT branch renders at the command's real font size
     (`_engine2d_draw_ir_text_font_size(computed_style)`, default 12) via
     `engine.draw_text`, honoring the command color. On Metal fast (gpu-only)
     mode this routes through the existing GPU glyph path
     (`MetalBackend.draw_text` -> `_dispatch_metal_text`), so glyph ink lands in
     the GPU framebuffer read back by `read_pixels_gpu_only`.
   Non-fast / software primitive rendering is untouched (opaque rects and the
   cpu-metal primitive parity scenes are unaffected).

## Verification
Probe: `simple_web_layout_render_html_pixels_engine2d("<div ...>HELLO WORLD</div>",
400, 200, "metal")`, text-run bbox 8,8 105x36 (3780 px):

- BEFORE: `zero_bar_px=3780 (100%)  fg_glyph_ink_px=0` -> RESULT: BAR.
- AFTER:  `zero_bar_px=0  fg_glyph_ink_px=494 (13%)  white_bg_px=3286` -> RESULT:
  GLYPHS (glyph-like ink density within the required 3%-60% band, no bar).

Gates (macOS, real Metal GPU):
- `scripts/check/check-engine2d-nomirror-fast-render-evidence.shs` -> pass
  (native-fast-bitexact; correctness mism=0, wm_routing mism=0).
- `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs` -> pass
  (cpu-metal-bitexact).
- Regression specs: simple_web_renderer_spec (79 pass), child_index_spec
  (21 pass), draw_ir_adv_spec (3 pass / 1 fail -- the failure is pre-existing and
  unrelated, reproduced identically on the pre-change executor).

# Shaped Devanagari runs at device scale 4 miss Chrome's ink (2026-11-23)

**Status:** open. **Red spec:** `test/01_unit/browser_engine/devanagari_render_k4_chrome159_spec.spl`
(`@tag:in-development`, Chrome 159 k=4 ink boxes for the ten render-table words).

At 1x the glyph runs (ids, pen x, mark y) and the right/bottom ink edges of
these words equal Chrome's. At k=4 (384 dpi) three separate defects show.
Measured on the GSUB lane head (general dev2 shaper) plus this lane, cpu lane;
the k=4 Chrome capture was validated by reproducing the 1x table at factor 1.

## 1. Pen x snapped in CSS px, then scaled (owner: shaped-run payload + `draw_ir_device_scale`)
`shaped_run_to_font_glyph_run` (`src/lib/skia/feature/shaper/shaper.spl`)
stores `xs` as whole CSS px; `draw_ir_device_scale.spl` multiplies them by k.
Device pen = 4*floor(p) where Chrome uses floor(4p):

| word | glyph pen px | Simple 4*floor | Chrome floor(4p) | x1 Simple / Chrome |
|------|--------------|----------------|------------------|--------------------|
| ड़ुँ  | 101 @ 8.768  | 32 | 35 | 114 / 117 |
| द्धू  | 35 @ 13.552  | 52 | 54 | 140 / 142 |
| नहीं  | 635 @ 17.376 | 68 | 69 | 165 / 166 |
| कुछ  | 62 @ 12.288  | 48 | 49 | 173 / 174 |

The Latin control `Hxgl` (unshaped path) is also 2 device px short on x1
(201 vs 203), so the class is not Devanagari-only.
Design: carry the fractional pen (26.6, `position.x * 64`) beside `xs` in
`DrawIrGlyphRunPayload` and let `draw_ir_device_scale` compute
`floor(x64 * k / 64)` (y: round). At k=1 that equals the current
truncate-x / round-y rule byte for byte, so 1x output cannot move. It touches
the shared Draw IR payload (SDN writer, paint-chunk snapshot, metal/vulkan
consumers), so it is a cross-backend change. Chrome also positions glyphs at
sub-pixel x at 1x (नहीं / कर्म 1x x1 41 vs 42); that needs sub-pixel glyph raster,
a separate step.

## 2. Shaped-run baseline 1 device px high (owner: font_renderer selected-run stager)
Every shaped word's top ink row is 1-2 device px above Chrome's at k=4 and
its bottom row 1 above on eight of ten words (हिन्दी 120..186 vs 121..187;
कुछ and टुँ keep Chrome's bottom row 195), while the Latin control's rows are equal
(132..192 both). Suspected (not verified): `_stage_selected_glyph_run_active`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`) takes its baseline from
the run face's ascent measured at k x font-size (`sfnt_measure_glyph_into`
meta[17]); the unshaped path places the baseline from the line metrics.
Not yet located which rounding differs.

## 3. Empty buffer when a command is skipped at k=4 (owner: web device-scale path)
`simple_web_layout_render_html_pixels_engine2d_at_device_scale`
(`simple_web_layout_engine2d_fast.spl`) returns `[]` when
`skipped_command_count != 0`. A shaped Devanagari command the stager declines
(हिंदी: glyph 785 is empty, so `glyph.width <= 0` invalidates the run; before
the general dev2 shaper every word but हिन्दी) therefore yields no frame at
k=4, while 1x paints the per-codepoint fallback.

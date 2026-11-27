# Devanagari glyphs are y-hinted with Latin blue zones (2026-11-22)

**Status:** open. **Owner lane:** glyph raster (`src/lib/common/encoding/sfnt_glyf.spl`).
**Red spec:** `test/01_unit/browser_engine/devanagari_glyph_hint_chrome159_spec.spl` (`@tag:in-development`).

## Symptom
`हिन्दी`, 16 px, `lang="hi"` (bundled Noto Sans Devanagari on both sides), div at left 20 / top 30, 1x:

| | ink x | ink y | headline rows |
|---|---|---|---|
| Chrome 159 | 19..50 | 30..45 | 34 dark, 35 grey |
| Simple | 19..50 | 28..45 | 33 grey, 34 dark |

Verified: glyph ids, pen x, the right ink column and the bottom ink row equal Chrome's
(`devanagari_render_chrome159_spec.spl` AC-1). Only the rows above the
headline differ: Simple's i-matra and ii-matra hooks are 1-2 rows taller.

## Cause (Latin knots applied: verified; that they account for both rows: inferred)
`_lcd_hint_knots` derives its font-y to pixel-y knots from the face's Latin
`x`, `o`, `H`, `O`, `l`, `p`, `g` outlines. Noto Sans Devanagari carries Latin (cmap x=1103, o=1047, H=881)
glyphs, so the knots exist and every Devanagari glyph is warped by Latin
x-height / cap-height zones. FreeType's autohinter (Chrome) picks the style
per glyph script and hints Devanagari with its own blue zones (headline top
and bottom, base-character bottom, below-base bottom).

## Fix sketch
Key the hint knots by (face, size, script of the glyph). For Devanagari build
the zones from the face's own reference outlines as FreeType's `deva` style
does (top of the headline from क म अ आ थ ध भ श, base bottom from the same
set), fit the scale on the headline-to-base height, and keep the Latin knots
for Latin glyphs of the same face. Measure each zone in Chrome first.

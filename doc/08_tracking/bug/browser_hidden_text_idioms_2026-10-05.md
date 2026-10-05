# Text hidden by the image-replacement idioms was painted (2026-10-05)

Status: FIXED for `color: transparent` and negative `text-indent`
(branch `work/browser-hidden-text`); one related gap still open (below).

Gap L of the 2026-10-05 five-site re-test
(`browser_real_site_rendering_gaps_2026-10-04.md`). wikipedia.org draws
its wordmark and its "The Free Encyclopedia" slogan from a background
sprite, and hides the real text with
`.central-textlogo__image{color:transparent;overflow:hidden;text-indent:-10000px}`.
The Simple browser painted that text over the page, clipped mid-word.

## Root causes

1. **`color: transparent` was ignored.** `parse_color` returns `0` both for
   `transparent` and for unparsable input, and both color setters
   (`declarations.spl`, `decl_apply.spl`) skipped a `0` result, so the
   element kept its inherited color. Separately, the glyph painters ignore
   color alpha entirely: `rgba(255,0,0,0)` painted fully opaque red.
2. **`text-indent` was ignored on the Draw IR lane.** The CPU raster loop has
   always placed line 0 at `text_x + st.text_indent_px`; the Draw IR
   emitters (`paint_layout.spl`), which BrowserSession pages go through,
   used the content-box left edge.

## Fix

- The keyword `transparent` now sets the fully transparent color (`0`);
  unparsable values still leave the color unchanged.
- `html_text_paint_fully_transparent` (layout_foundation): a `#text` run
  whose color has alpha 0 and no text-shadow paints nothing on either lane
  (`_html_draw_ir_visible`, and the CPU raster `#text` branch).
- Draw IR first/single lines start at `content_x + text_indent_px` with the
  width reduced by the same amount, matching the raster loop. With no
  indent, the result is unchanged.

Spec: `test/01_unit/browser_engine/simple_web_hidden_text_spec.spl`
(4/4; 2/4 on main -- the transparent and indent cases fail there).

## Still open

- **Partial alpha.** `rgba(..., 0.5)` text paints fully opaque: the glyph
  painters ignore color alpha. Only alpha 0 is handled (by not painting).
  Unblock: honor command color alpha in the Engine2D text batch and the
  CPU `fb_text_*` painters.
- **Transparent text with a text-shadow** still paints the glyphs (CSS draws
  only the shadow).
- **R (separate fix).** A text-only `<div>` page with a background paints no
  text at all on the static CPU lane. That lane
  (`simple_web_engine2d_render_html_pixels`) only lays out a "text
  document" (one containing `<p`, `<h1-3`, `<span`, ...); for anything else it
  falls back to a substring heuristic that fills the background and paints
  no text. This spec therefore keeps the body without a background. Fixed
  separately by deleting the heuristic.

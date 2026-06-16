# Bug: web renderer does not soft-wrap long lines (right-edge clipping)

- **Id:** web_render_no_line_wrapping_right_edge_clip_2026-06-16
- **Status:** open
- **Priority:** P2
- **Area:** `lib/gc_async_mut/gpu/browser_engine` (web HTML layout renderer)
- **Found via:** rendering `md_wysiwyg_graphical_render_tldr.md` to a 480-wide PPM

## Symptom

Long text lines run off the right edge of the framebuffer and are clipped
instead of wrapping to the next line. In the rendered TL;DR page, lines like
`Render markdown to pixels (headless PPM or a win…`, `…engine2d_b`, and
`headless    PPM framebuff…` are visibly cut off at the page width.

## Expected

A block-flow inline run wider than its containing block should soft-wrap at word
boundaries (CSS normal white-space) onto additional line boxes, advancing the
block height — matching browser behavior the renderer otherwise mirrors.

## Notes

- The renderer derives layout geometry from `glyph_scale()` and already computes
  per-glyph advance (`char_w`), so the wrap point is computable; what is missing
  is breaking the inline run into multiple line boxes when the accumulated
  advance exceeds the content width.
- Reproduce: `bin/simple run src/app/office/md_wysiwyg_ppm.spl <any long-line .md>
  /tmp/out.ppm` at a width narrower than the longest line.

## Impact

Markdown/HTML with prose lines wider than the viewport loses trailing content in
the raster output. Workaround today: render at a width ≥ the longest line.

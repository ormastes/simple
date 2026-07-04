# Bug: web renderer does not soft-wrap long lines (right-edge clipping)

- **Id:** web_render_no_line_wrapping_right_edge_clip_2026-06-16
- **Status:** RESOLVED (2026-06-16)
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

## Root cause (confirmed)

The renderer *did* wrap, but at the wrong width. In the block-flow inline-run
path of `layout()`, an inline `#text` child was laid out at its full INTRINSIC
(unwrapped) width, not the available content width. Measured live (480-wide
surface): the `<p>` block was `w=480` but its text child was `w=690`, so
`cpl = 690 / char_w = 57` chars/line — the first wrapped line was ~684 px wide
and clipped against the 480 px surface, then the remainder wrapped to line 2.

## Fix

Bound the inline `#text` layout width to the available content width
(`iw - inline_x`) before laying it out, unless `white-space: nowrap`. Short
inline pieces (intrinsic ≤ available) are unaffected. After the fix the text
child is `w=480` and wraps within the surface. Ink-preservation oracle at fix
time (same text at 240×400 vs 960×120): both render 3720 ink px with the fix (no
glyph lost); without it the narrow render drops to 2060 (~45% clipped). Regression
suite `test/01_unit/browser_engine/` unchanged (34 pass / 45 pre-existing fail).

The live regression oracle in `test/01_unit/app/office/md_wysiwyg_render_spec.spl`
was later resized (narrow 240×100, wide 480×64, shorter text) to fit the
interpreter-bound web-layout perf budget under the test runner; it still asserts
narrow-vs-wide ink preservation, just over fewer blank rows.

Note: per-line *break-on-overflow within a single inline run mixing multiple
pieces* is still simplistic, but single-text-child blocks (paragraphs, headings,
list items) now wrap correctly within the surface.

## Reproduce

`bin/simple run src/app/office/md_wysiwyg_ppm.spl <any long-line .md> /tmp/out.ppm`
at a width narrower than the longest line.

# Inline-run x advance disagrees with Chrome: plain text over-measured, bold under-measured

- Status: OPEN
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
  (`intrinsic_text_width`, `inline_text_advance_width`, `style_text_advance`)
- Found by: `scripts/check/check-chrome-layout-geometry-diff.shs` at `GEOM_DIFF_HEIGHT=20000`

This is the whole remaining mismatch set on `overview.html` (5 of 5 rows) after
the round-3 vertical fix in
`web_inline_box_takes_line_height_not_content_area_2026-09-12.md`, and it is a
DIFFERENT cause from that one — flow positioning is now correct; the advances
are not.

## Evidence (900 px, font `16px/1.5`, `<p>Paragraph with <strong>strong</strong>, …`)

| element | Chrome x | Simple x | dx | Chrome w | Simple w | dw |
|---|---|---|---|---|---|---|
| `strong` | 113 | 140 | 27 | 51 | 43 | 8 |
| `em` | 173 | 198 | 25 | 69 | 68 | 1 |
| `a` | 295 | 331 | 36 | 111 | 108 | 3 |

Two independent errors, in opposite directions:

1. **Plain text is over-measured.** The leading run `"Paragraph with "` is
   112 px in Chrome and ~140 px in Simple — about 25 % wide. `style_text_advance`
   derives a single per-codepoint advance from the font size; real proportional
   metrics vary per glyph, and the flat advance is too generous.
2. **Bold is under-measured.** `<strong>strong</strong>` is 51 px in Chrome and
   43 px in Simple: the `font-weight: bold` face's wider advances are not
   applied at all — the styled run measures as if it were regular.

The dx column growing (27 → 25 → 36) is the accumulation of (1) across the
successive plain-text runs between the styled ones, not a per-boundary
whitespace bug: the per-element `dw` stays near zero for the runs whose face
Simple measures correctly.

## Why it was not fixed in round 3

`style_text_advance` is on every text path in the renderer, including paint and
wrapping. Changing it moves the width of every text box on every page at once,
so it needs its own before/after pixel-differ pass over all 8 catalog pages
rather than being folded into a layout-flow change. `Style` already carries
`resolved_font_advances` / `resolved_font_width` for the real-metrics path; the
work is to make that path cover these runs (including the bold/italic faces)
instead of falling back to the flat advance.

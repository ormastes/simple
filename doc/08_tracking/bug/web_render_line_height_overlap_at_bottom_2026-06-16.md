# Bug: web renderer overlaps text lines near the bottom of the page

- **Id:** web_render_line_height_overlap_at_bottom_2026-06-16
- **Status:** RESOLVED (2026-06-16)
- **Priority:** P3
- **Area:** `lib/gc_async_mut/gpu/browser_engine` (web HTML layout renderer)
- **Found via:** rendering `md_wysiwyg_graphical_render_tldr.md` to a 480x600 PPM

## Symptom

Toward the bottom of the rendered page, two text lines overprint each other:
`default 900x760)` overlaps a following path line, producing a smeared,
unreadable region. The top and middle of the page advance lines cleanly; the
defect appears only in the lower portion.

## Root cause (confirmed)

The block-flow inline-run path in `simple_web_html_layout_renderer.spl` `layout()`
overwrote a `#text` child's height with a SINGLE line:
`out_bh[c] = style_line_h(cst)`, and advanced the block cursor by one
`inline_line_h`. When that text wrapped to N lines (common for long heading or
prose lines narrower than the text), the block reserved only one line of height,
so the next sibling block was placed over the wrapped tail.

Measured live (480-wide) on `<h1>long…</h1><p>…</p>`: the h1 reported `h=36`
(one line) while its text wrapped to 2 lines and painted to `y≈79`; the `<p>`
was placed at `y=62` → ~17 px overlap.

## Fix

Reserve the WRAPPED height: `out_bh[c] = max(1, out_wrap_starts[c].len()) *
style_line_h(cst)`. Single-line text is unchanged (`wrap_lines == 1`); multi-line
text now reserves N lines, so the inline run height and cursor advance are
correct. After the fix the same case reports h1 `h=72` and the `<p>` at `y=88`
(no overlap). Regression suite `test/01_unit/browser_engine/` is unchanged
(34 pass / 45 pre-existing fail, identical before and after — net-zero).

## Expected

Each block/line box advances `y` by its full computed line-height (plus margins)
so no two lines share vertical space, consistently down the whole page.

## Reproduce

`PAGE_W=480 PAGE_H=600 bin/simple run src/app/office/md_wysiwyg_ppm.spl
doc/07_guide/ui/md_wysiwyg_graphical_render_tldr.md /tmp/out.ppm`, then inspect
the lower third of `/tmp/out.ppm`.

## Impact

Multi-block documents can become unreadable in their lower region. Cosmetic vs.
the entity/wrap bugs, but it corrupts content legibility where it occurs.

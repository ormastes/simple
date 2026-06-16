# Bug: web renderer overlaps text lines near the bottom of the page

- **Id:** web_render_line_height_overlap_at_bottom_2026-06-16
- **Status:** open
- **Priority:** P3
- **Area:** `lib/gc_async_mut/gpu/browser_engine` (web HTML layout renderer)
- **Found via:** rendering `md_wysiwyg_graphical_render_tldr.md` to a 480x600 PPM

## Symptom

Toward the bottom of the rendered page, two text lines overprint each other:
`default 900x760)` overlaps a following path line, producing a smeared,
unreadable region. The top and middle of the page advance lines cleanly; the
defect appears only in the lower portion.

## Suspected cause

Vertical advance (line-height / block-margin accumulation) appears to under-count
for later blocks — likely a rounding or margin-collapse interaction in the block
layout pass so successive line boxes are placed with insufficient `y` separation
as the cumulative offset grows. Heading blocks (larger `font_size`/line-height)
just above the overlap are a likely contributor.

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

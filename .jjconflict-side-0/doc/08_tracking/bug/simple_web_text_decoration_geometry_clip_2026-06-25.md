# Simple Web Text Decoration Geometry Clip Blocker

Date: 2026-06-25

## Status

Open.

## Summary

`text-decoration-thickness` and `text-underline-offset` cannot be safely marked
implemented yet. A scoped attempt to add both properties to the Simple Web HTML
layout renderer made the renderer SSpec fail even after switching from an 8px
fixture to a 16px fixture with larger line-height.

## Evidence

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` passed after adding the geometry fields.
- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --mode=interpreter --clean` failed with the new geometry examples.
- Failure shape: the existing underline color behavior remained stable, but
  thickness/offset pixel witnesses did not prove changed visible geometry under
  the current text paint clip/line box behavior.

## Suspected Cause

Underline paint geometry is tied to text ink position and the current paint
clip. Larger thickness or positive offset can be clipped or collapse to the
same visible pixels, so simply changing the underline rectangle height/y
coordinate is not sufficient.

## Required Fix

Before claiming support for `text-decoration-thickness` or
`text-underline-offset`:

- Define underline decoration ink bounds separately from glyph ink bounds.
- Ensure the paint clip includes decoration overflow when CSS line-height permits it.
- Add pixel SSpecs that prove:
  - default underline remains unchanged;
  - thicker underline increases visible decoration pixels;
  - underline offset moves the decoration without clipping it away.
- Then move both properties from unsupported inventory to implemented inventory.

## Non-Solution

Do not add the properties to `CSS_SUPPORTED` as no-ops. That would make
traceability report support that the renderer cannot prove.

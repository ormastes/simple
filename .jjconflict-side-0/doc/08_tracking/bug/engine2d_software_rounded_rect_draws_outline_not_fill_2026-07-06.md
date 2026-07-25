# SoftwareBackend.draw_rounded_rect draws an OUTLINE where it must FILL

## Status
Fixed (2026-07-06).

## Severity
High — semantic rendering bug. Any filled rounded-rect UI element (buttons,
cards, pills, panels) drawn through the software backend renders as a hollow
1px outline instead of a solid shape.

## Summary
`SoftwareBackend.draw_rounded_rect` (`src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:273`)
rendered only the four 1px edges (`sw_hline`/`sw_vline`) plus corner-arc
outlines — a hollow rounded rectangle. The `RenderBackend` contract for
`draw_rounded_rect` is a FILLED shape, and the canonical reference
`emu_draw_rounded_rect` (`backend_emu.spl:152`) fills the body with three rect
bands + four FILLED corner arcs.

A separate `draw_rounded_rect_outline` method already exists
(`backend_software.spl:545`) for genuine outlines, so `draw_rounded_rect`
emitting an outline is an unambiguous bug, not a design choice.

## Evidence
Measured on the shared-raster parity harness fixture (48x48 surface,
`draw_rounded_rect(6, 6, 30, 24, 6, 0xFFFF0000)`):

| Path | non-background pixels |
|------|-----------------------|
| `SoftwareBackend.draw_rounded_rect` (outline, buggy) | 92 |
| `emu_draw_rounded_rect` (fill, canonical) | 680 |
| pixel mismatch (sw vs emu) | 604 |

604 of the shape's pixels are wrong — the entire interior is unpainted.

## Fix
`SoftwareBackend.draw_rounded_rect` now delegates to
`emu_draw_rounded_rect(self, x, y, w, h, radius, color)`, the same idiom already
used by `draw_ellipse`/`draw_ellipse_filled` in this file. Delegation composes
the fill from `core.draw_rect_filled` (trait dispatch, so `self` mutation
persists) and is byte-identical to the canonical algorithm by construction.
`draw_rounded_rect_outline` is left untouched for genuine outlines.

## Verification
`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`:
`cmp_rounded_rect()` now returns 0 (was 604). The harness assertion for
`draw_rounded_rect` was flipped from `> 0` (pinned divergence) to `== 0`
(byte-exact) and stays green.

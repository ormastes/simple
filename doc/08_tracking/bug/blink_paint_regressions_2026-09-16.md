# blink paint pipeline behavioral regressions

Date: 2026-09-16

## Observed
After fixing spec-side issues (stale `std.lib.blink` import prefix, `val` vs
`var` array mutability), three specs still fail on behavior:

- `test/01_unit/lib/blink/paint_tree_walker_spec.spl` — "background color with
  a>0 emits a DrawRect op in the canvas' recorder": expected >0 ops, got 0;
  "full walk of 2 boxes emits 2 DrawRect ops": expected 2, got 0. (4 of 6 now
  pass; these 2 emit nothing into the recorder.)
- `test/01_unit/lib/blink/paint/text_paint_spec.spl` — "paints a real,
  non-uniform glyph pattern for a single letter — sabotage oracle": expected
  true, got false (1 of 4 fails).
- `test/01_unit/lib/blink/render_lane_pixels_spec.spl` — "the boundary just
  outside the div's right/bottom edge is blue, not red": pixel read returned 0
  (transparent) where 4278190335 (0xFF0000FF blue) was expected (1 of 3 fails).

## Impact
The blink paint path drops ops/pixels at specific boundaries: recorder-based
emission under `paint_box`, single-glyph raster coverage, and the pixel just
outside a laid-out div's edge. HTML+CSS-to-pixels fidelity claims cannot be
relied on at these edges.

## Expectation
All three specs pass as pinned: ops recorded for a>0 backgrounds and multi-box
walks, non-uniform glyph pattern for a single letter, and body background
(blue) present on boundary pixels adjacent to the div.

## Unblock condition
Fix the op-recording path in `src/lib/blink/paint/` (paint_box / tree walker
recorder wiring) and the lane rasterizer's edge/coverage handling, then re-run
the three specs — no spec change should be needed.

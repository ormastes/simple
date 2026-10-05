# skia CPU `fill_path_aa`: fake vertical AA, edges quantized to rows; 8-step `_sqrt`

- **Found:** 2026-10-05, while scoping SVG rendering on the skia CPU backend.
- **Status:** fixed in the change that adds this record.

## Defects

1. `src/lib/skia/backend/cpu/raster_prims.spl` `_make_edge` stored
   `y_min = ceil(y0)`, `y_max = ceil(y1)` — every edge snapped to integer
   rows, so a shape spanning y 10.25..10.75 produced no rows at all and every
   horizontal edge was aliased.
2. `fill_path_aa`'s "4-subrow supersampling" called `_scan_row(..., py)` four
   times with the SAME integer `py`. Fully covered pixels were simply written
   four times; partially covered pixels were `blend_pixel`-ed four times with
   the same coverage, so a 50 % pixel came out 1 - 0.5^4 = 94 % opaque.
3. Full coverage used `set_pixel`, which overwrites the destination: a
   translucent fill replaced what was underneath instead of blending.
4. Open subpaths were not implicitly closed for filling (Skia/SVG fill
   semantics close every contour), so an unclosed polygon filled garbage.
5. `_sqrt` in `feature/stroke/expand.spl`, `feature/stroke/dash.spl` and
   `backend/cpu/shaders.spl` ran 8 Newton steps from `x / 2`, which has not
   converged for x above ~1e4: `_sqrt(1e6)` returned ~2000. Long stroke
   segments got half-width normals, long dashes were laid out against twice
   the true length, and radial gradients past ~100 px were wrong.

## Fix

Edges keep fractional y; each row is sampled on 4 sub-scanlines at
`row + (k + 0.5) / 4`, inside spans add their exact horizontal overlap into a
coverage row, and each touched pixel is blended once with coverage clamped
to 1. Contours are implicitly closed. The three `_sqrt` helpers delegate to
`std.common.math.special.sqrt_f64`.

## Specs

- Reproducer + generalization: `test/01_unit/lib/skia/fill_path_aa_coverage_spec.spl`
  (sub-pixel height, half-covered column blended once, even-odd hole with
  fractional edges, diagonal area conservation, implicit close, translucent
  blend, 1000 px stroke offset, 1000 px dash count).
- Existing skia specs unchanged in verdict: raster_prims, cpu_backend,
  engine2d_bridge, stroke_expand, surface, cc tile.
- `test/01_unit/lib/skia/stroke_dash_spec.spl` "uniform dash on a long
  horizontal line produces N sub-segments" was RED before (12 dashes for 10)
  because of defect 5; it is GREEN now. Its remaining RED case ("pattern
  [0, 10] produces empty path") is unrelated and unchanged.

## Goldens and perf

- The reftest parity goldens (`test/03_system/gui/reftest/parity/goldens/`)
  are code, not stored pixels, and none of them currently runs: they call
  `sk_color_red()` without its argument (`reftest_spec` is 2/14 before and
  after, identical case list), so no golden output changed. Visual
  before/after check instead: a probe scene (winding + even-odd stars,
  translucent cubic circle over them, 12 thin strokes, round-capped 236 px
  stroke, dashed stroke, sub-pixel strip, half-pixel-offset rectangle)
  dumped to PNG and inspected — after the fix the translucent fill blends,
  the 0.5 px strip appears, rectangle edges are anti-aliased and the dashes
  are evenly spaced to the end of the line.
- Interpreted, the same scene x5 rendered in 26.4 s before and 13.3 s
  after (one blend per pixel instead of four scanline passes).

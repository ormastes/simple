# css-paint first table: residual is glyph AA + 1-level gradient, not row geometry (2026-11-19)

Diagnosis (1x catalog, css-paint 2.38%, 900x760 crop, Simple binary webrender-blend, Chrome 159):

| quantity | Chrome | Simple |
|---|---|---|
| horizontal rules y (x=100) | 121, 162, 203, 244 | 121, 162, 203, 244 |
| text ink rows, header row | 135-146 | 135-146 |
| text ink rows, body row 1 | 176-187 | 176-187 |
| text ink rows, body row 2 | 217-231 | 217-231 |
| ink x extents per row | 55-494 / 55-470 / 56-476 | 55-494 / 55-470 / 56-476 |

Row heights (41 px), rule positions, cell text vertical offsets and horizontal extents are
pixel-identical. There is no row-height, baseline or border-collapse defect to fix.

The ~6.4k differing pixels in rows 100-272 (any channel delta) split into:
- ~3.1k inside the three text bands: glyph antialiasing / ink-coverage differences
  (e.g. header band 528 Chrome ink px vs 515 Simple, 3 px "dark" threshold). Rasterizer lane, not layout.
- ~3.3k outside text bands: 1-level (255 vs 254, 252 vs 251) differences along a soft gradient
  at y 233-248 (and x 40-860) plus a 1-level tint (229,233,247 vs 229,233,246) at x=20; these are
  below any visible threshold and come from a blurred shadow/gradient quantization difference.
  The constant ~160 px per 40-column strip at rows 232-248 is this 1-level band.

Next lever: text glyph coverage (rasterizer) and blur/gradient rounding, not table layout.
Method: PIL scratch scripts over `check-chrome-catalog-pixel-diff.shs --pages css-paint --out`.

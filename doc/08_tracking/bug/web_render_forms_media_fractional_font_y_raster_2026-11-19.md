# forms-media 1x (2.16%): fractional font sizes raster y at the integer size

Date: 2026-11-19. Page: `examples/06_io/ui/web_catalog/forms-media.html`, 900x760 crop, Chrome 159, 1x.
Base: origin/release/1.0.0 32ddc119ffc, seed `cargo-target-webrender-blend`.

## Ranking (8,202 px with delta > 24, clustered on an 8 px grid)

| # | box (x0,y0-x1,y1) | element / feature | px | kind |
|---|---|---|---|---|
| 1 | 120,436-337,452 | `h3` "Feature examples and support", bold 18.72 px | 769 | glyph raster; ink bbox equal (right edge 337 vs 336) |
| 2 | 48,121-141,178 | `Name` label, `Simple` value, `Enabled` label | 600 | LCD glyph AA; row profile within a few % |
| 3 | 91,257-203,289 | `<textarea>` "Editable text", DejaVu Sans Mono 13.333 px | 533 | vertical glyph raster, 1 row (see below) |
| 4 | 473,544-763,559 | feature list `owner=...` text | 481 | LCD glyph AA |
| 5 | 68,332-205,384 | `Exercise controls` button + `Not exercised` | 461 | LCD glyph AA |

Then three identical 390 px clusters (109,584/664/744-414) = the `No complete rendering claim` `<p>` rows, and a 395 px `owner=` line. A best-shift search (+-3 px) on every top-12 box left the zero-shift score as the best one, and every cluster's ink bbox equals Chrome's: none of these is a layout offset. Nothing in the top 5 is a known big-model item except in the sense that all of it is glyph raster.

## Root cause of #3 (and, by the same mechanism, #1)

Textarea text (`monospace` = DejaVu Sans Mono at the UA 13.3333 px) is 9 ink rows tall here, 10 in Chrome; the baseline row is the same.

| `font-family:monospace`, `HEHEHE`, ink rows | Simple | Chrome |
|---|---|---|
| 13 px | 23..31 | 23..31 |
| 13.3333 px | 23..31 | 22..31 |
| 16 px | 23..34 | 23..34 |
| 12 / 20 / 14 / 15 / 10 / 18 / 24 px | equal | equal |

Only the fractional size differs, in a plain `div` as well as in the textarea (so it is not a textarea layout offset: line pitch 15 and the box edges match; default textarea ink rows Chrome 24-34 / 39-49, Simple 25-35 / 40-50 with the E bar at 27 vs 28). Sans-serif at 13.3333 px is equal, because Liberation Sans' cap height rounds to the same row count at 13 and 13.333.

`src/lib/common/encoding/sfnt_glyf.spl` (LCD raster, around line 1700-1736): `size_px` is an integer; a fractional size reaches it only as `x_milli`, which `_scale_commands_x` applies to x (`x_frac` / `x_ratio`). `scale = size_px / units_per_em` and `_lcd_hint_knots_cached(font, ..., size_px)` (line 1405, key `...|{size_px}`; knots built at line 1313) are both at 13, so cap height is 0.729 x 13 = 9.48 -> 9 rows where Chrome hints 0.729 x 13.333 = 9.72 -> 10. The 18.72 px `h3` (#1) is the same class (the css-paint note in `web_render_css_parity/skill.md`, "~7% the 18.72px h3 (integer font-si...").

## What a fix needs (why this lane stopped)

Carry the fractional size into y: `scale` from `size_milli / (1000 * units_per_em)`, `_lcd_hint_knots` with a fractional `size_px` (its `size_px >= 6 and <= 14` threshold, the 1.25 px growth cap and the 26.6 rounding all take the size), the `_lcd_hint_cache` key and every glyph-atlas key and bitmap height/bearing derived from `size_px`, and `x_frac` goes away. That is a change to the shared glyph raster for every fractional-size run (UA control fonts, `h1`-`h6` 0.67-2em, `em` sizes), and it must be re-measured on all eight catalog pages and the matrix, not a one-feature patch under 60 lines. Measure first with `HEHEHE` rows at 13.3333, 18.72, 10.6667, 14.4 px mono and sans, bold and regular, against Chrome 159.

Not a fix: `line-height: normal` for the textarea UA style (`declarations.spl` ~1756) changes nothing (tried, reverted).

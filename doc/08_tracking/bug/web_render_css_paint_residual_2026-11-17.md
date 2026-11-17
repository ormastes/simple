# css-paint residual vs Chrome 159 (5.68% at 1x) - classification, 2026-11-17

Status: classes 1 and 3 (vertical drift from fractional block margins) FIXED 2026-11-17, see skill doc "block-axis margins carry fractions" and spec block_fractional_margin_chrome159_spec; class 2 (fractional font size) and class 5 stay open.
Setup: seed `cargo-target-webrender-vk`, cpu_simd, Chrome 159.0.8154.6, 900x760, tolerance 8 per channel
(`pixel_diff.spl`). Reproduced 38,905 px = 5.688% (gate says 5.68).

## Partition of the 38,905 mismatching px

| # | class | px | share | contained? |
|---|-------|----|-------|-----------|
| 1 | Vertical drift from fractional layout, y >= 330: whole list/intro text sits 1 row low. Credited as dy=0 -> dy=+1 on that region: 33,232 -> 26,717 | 6,515 | 16.7% | no (see below) |
| 2 | h3 `Feature examples and support` (18.72px bold): ink 1 row high and ~5 px wider (Chrome x 67..336, Simple 67..341). `Style.font_size` is `i32`, so 18.72 -> 19 | ~2,800 | 7.2% | no (fractional font size) |
| 3 | h2 `Table` ink 1 row high | 351 | 0.9% | no (same cause as 1/2) |
| 4 | Box edges: rows 24-36 (section top border/corners), 245-257 (table bottom) | ~156 | 0.4% | not examined, tiny |
| 5 | Glyph residual in aligned text (list region 26,717 after the shift, plus table cells ~2,410): LCD mask diffs, vertical stem hinting (Chrome snaps horizontal strokes to whole rows), pen phase | ~29,100 | ~74.8% | excluded: pen phases owned by another agent; vertical hinting is font_renderer work, not contained |

Classes 1-4 plus 5 are a partition (overlaps removed): 6,515 + ~2,800 + 351 + ~156 + remainder = 38,905.
Class 5 is the remainder, so its figure carries the rounding of the other four.
After the +1 alignment the surviving large-delta pixels (>64) in the list region drop 19.4k -> 10.3k, but the
small-delta mass (AA/LCD, delta 9-64) stays, which is why the shift is worth only 16.7%.

Row-profile check (sum of ink per row, list line at y 436..460): Chrome x-height top row 7, Simple row 8; the
18 rows between match to within ~5% once shifted. Probe page of plain `<p>` blocks (sizes 12/14/16/20/24, lh 1.5, normal,
20px) matches Chrome row-for-row at 16, 20, 24, 12 px, so the glyph baseline rule is right and the drift is
introduced by the box y.

## Root cause of class 1 (and 2, 3)

Chrome `getBoundingClientRect().y` (1/64 LayoutUnit) vs Simple layout y (i32):

| box | Chrome y | Simple y |
|-----|----------|----------|
| h2 | 64.906 | 65 |
| table | 120.81 | 121 |
| h3 | 284.53 | 285 |
| first p | 331.33 | 332 |
| first li | 395.33 | 396 |

Sources: h2 `0.83em` margins (19.92), h3 `1em` margins (18.72), h3 line-height 28.08. Simple rounds each box
(error grows +0.09 -> +0.67 px) and crosses the paint-rounding threshold at the first p; Chrome paints it at 331.
(Widths from a no-`--hide-scrollbars` dump-dom run are 15 px short and were not used.)

No per-value rounding rule works: rounding gives the p at 332 (Chrome 331); flooring gives the h2 at 64 (Chrome 65).
Any fix must carry a sub-pixel remainder.

## Fix sketch and why it was not attempted

Keeping box heights integer and carrying only fractional margins through the block cursor gives 64.92, 120.84,
284.56, 331.28, 395.28, which round to 65, 121, 285, 331, 395: exactly Chrome's painted rows on this page.
Scope: margin resolution plus the block-flow cursor, NOT a full LayoutUnit port.
Not contained today: `Style.margin_t/margin_b` and `font_size` are `i32` at cascade time; no milli margin
survives the cascade (only `line_height_em_milli`); `layout_engine.spl` has 126 and `layout_foundation.spl` 24 references
to `margin_t`/`margin_b` across the main loop, first-child collapse, `leading_margin_t`, trial layout and float bands.
A carry in one path would make two paths measure the same thing differently (the recurring failure in the skill
doc). Needs a reviewed design: a milli margin field, carried by every block-flow path together.
Class 2 additionally needs fractional font sizes through `resolve_font_metrics` and the rasterizer.

No spec, code change, catalog run or matrix run was made (nothing to prove without a change).

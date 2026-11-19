# web render: auto-table column split uses integer max-content widths (1px column-edge shift)

**Status: RESOLVED 2026-11-19** (branch work/webrender-table-milli-split-20261119). `explicit_auto_table_column_offsets`
carries a per-column milli remainder (`col_frac`, `table_cell_text_frac_milli`) and distributes in x1000 units
(`table_distribute_auto_columns`, interpolation product widened to i64); only the cumulative column edges round.
Pinned by `table_auto_milli_column_split_chrome159_spec` (3 pages; Chrome 810px table at x=45: rules 45/422/854, base 423).
css-paint 1x 2.43 -> 2.38, dpr4 3.54 -> 3.51. Not carried: cells whose max-content comes from inline children (`<code>`),
which keep the whole-px width. Side effect: the plain UA table's third cell is 19 wide (Chrome snaps 45.6..65.4 to 46..65).


Date: 2026-11-19. Page: examples/06_io/ui/web_catalog/css-paint.html, 1x, Chrome 159, aarch64.

## Symptom
Largest single mismatch cluster on css-paint (2.43%): the leading `<table width:100%; border-collapse:collapse>`
(Feature/Expected, 3 rows). Cluster box x416..512, y112..256, 1595 differing pixels (delta>24).
The inner column rule is at x=416 in Chrome, x=417 in Simple, and the whole second column text is 1px right
(Chrome "Expected" at 425, Simple 426). Outer rules (x=45, x=854) match.

## Numbers (Chrome 159, measured by getBoundingClientRect, table left 45.5, avail 809)
- column widths 371.359 / 437.641 (boundary 416.859 -> collapsed 1px rule snaps to pixel 416).
- fractional max-content: bold "Feature" 57.797, bold "Expected" 71.141 (+16 padding +1 half-borders = 74.80 / 88.14).
  809 * 74.80/162.94 = 371.4.
- Simple: integer max-content 58+17=75, 71+17=88 -> 809*75/163 = 372.2 -> col edge 372 -> rule at 417.

## Root cause
`explicit_auto_table_column_offsets` (src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_foundation.spl:1804)
builds `widths`/`col_min` from the i32 `table_cell_max_content_width` (rounded to whole px), then
`table_distribute_auto_columns` (layout_table.spl:203, the `available > sum_max` branch at :248) shares the excess
in proportion to those rounded maxima. Rounding error of ~0.2-0.5px per column skews the proportional split by ~0.8px,
which flips the rounded boundary. The edge rounding itself already matches Chrome (see the :250 comment); only its input is lossy.

## What a fix needs
Carry max-content (and min-content) per cell in milli-px (the layout already has `cursor_advance_frac` / `*_milli`
helpers) through the width scan at foundation.spl:1819-1895 and distribute in i64 milli units in
`table_distribute_auto_columns`, rounding only the final boundaries. Cell padding/border halves are exact integers, so
only the text component needs milli precision. Estimated >60 lines across two files plus spec pins; not a small fix.
Pin candidates: the Chrome numbers above (column edge 371/416 for this table; also verify the 3-col
table_collapsed_border_paint_chrome159_spec 170.38 case still holds).

## css-paint mismatch ranking (delta>24 clusters, 8886 px total in the 900x760 compare)
1. table column-edge shift (this bug): 1595 px, x416-512 y112-256
2. intro paragraph glyph AA/subpixel: 1202 px, x64-832 y336-384
3. list item text (dt/code + owner= lines): 1015 px, x80-624 y576-624
4. list item text: 922 px, x80-528 y480-528
5. h3 "Feature examples and support" + heading region: 809 px, x64-352 y288-320
Remainder (~390 px each, 4 bands) are the repeated "No complete rendering claim..." lines: LCD text AA only, no layout offset.
Items 2-5 and the rest are text antialiasing deltas (glyph geometry matches visually), not layout shifts.

- 2026-11-19 re-probe at 1x (release/1.0.0 5876e8e16b6): css-paint first table inner column rule is at x=416 in both Chrome 159 and Simple (edges 416/417 identical, rule rows 122-347 identical); the x=417 offset is gone. Remaining css-paint mismatch in that table box (~6.1k px, 2.38% page) is vertical/text, not the column split.

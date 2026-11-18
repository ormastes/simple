# Web layout: percent padding is not parsed; grid bare `span N` and implicit-row stretch

Found 2026-11-18 while fixing grid item margins (Chrome 159 oracle, 900x2000,
`.g{display:grid;width:400px}`). Gaps 1 and 2 are RESOLVED (2026-11-18, spec
`test/01_unit/browser_engine/percent_padding_grid_span_chrome159_spec.spl`,
0/23 on base, 23/23 now). Gap 3 and the residue listed at the end stay open.

## 1. Percent padding is dropped engine-wide — RESOLVED

Was: `_padding_length_px` (`simple_web_html_layout_renderer_declarations.spl`)
accepted px, 0, em, rem, vw, vh. A `%` token returned -1, which dropped the
whole `padding` declaration, in every layout context (not only grid).

Now: a percent is kept as `Style.pad_{l,t,r,b}_pct` (percent x 1000, px slot 0)
and resolved by `style_with_resolved_percent_padding(st, containing_w)`
against the containing block inline size, on all four sides: the parent
content width (block, inline, inline-block, float, flex item), the grid AREA
width (grid item), the padding box (absolutely positioned). Shrink-to-fit
widths (inline-block, float, abspos, auto flex item) add the resolved
horizontal padding to the measured content (`percent_padding_extra_w`).

| case (x y w h in a 400 px container)          | Chrome 159   | base        | head    |
|-----------------------------------------------|--------------|-------------|---------|
| block `padding:10%`, 10 px child              | 0 0 400 90   | 0 0 400 10  | =Chrome |
| its child                                     | 40 40 320 10 | 0 0 400 10  | =Chrome |
| block `padding:5% 10% 25% 2%;height:10px`     | 0 0 400 130  | 0 0 400 10  | =Chrome |
| `width:50%;padding:10%`                       | 0 0 280 80   | 0 10 200 1  | =Chrome |
| same + `box-sizing:border-box;height:100px`   | 0 0 200 100  | 0 0 200 100 | =Chrome |
| its child                                     | 40 40 120 10 | 0 0 200 10  | =Chrome |
| nested child `padding:10%` (of 200)           | 40 40 200 50 | 0 0 200 10  | =Chrome |
| inline-block `width:100px;height:20px;padding:10%` | 0 0 180 100 | 0 0 100 20 | =Chrome |
| flex item `width:100px;height:20px;padding:10%` | 0 0 180 100 | 0 0 100 20 | =Chrome |
| flex item `flex:1;padding:5%` beside it       | 180 0 220 100 | 100 0 300 20 | =Chrome |
| grid item `padding:10%` in a 100 px track (`align-items:start`) | 0 0 100 20 | 0 10 100 1 | =Chrome |
| grid item `padding:5%` in the 300 px track    | 100 0 300 30 | 100 10 300 1 | =Chrome |
| grid item `padding-top:25%;height:10px` (100 px track) | 0 0 100 35 | 0 0 100 10 | =Chrome |
| abspos `width:50px;height:10px;padding:10%` (padding box 400) | 0 0 130 90 | 0 0 50 10 | =Chrome |
| float `width:100px;height:10px;padding:10%`   | 0 0 180 90   | 0 0 100 10  | =Chrome |
| auto-width float / abspos / flex item `padding:5% 10%` around a 50x10 box | 0 0 130 50 | 0 0 50 10 | =Chrome |

A page using `padding:10%` renders pixel-identical to the same page written
with the equivalent px padding (block text, inline span, flex row, column
flex, grid; cpu_simd 1x).

## 2. Bare `grid-column: span N` — RESOLVED

Was: `normalized_grid_placement` required a positive start line, so `span 2`
normalized to "" and the item was one track wide.

Now: `span N` normalizes to itself (auto start, N tracks), `span N / L` to the
definite range ending at line L; `grid_placement_start` reads a leading
`span` as auto; `grid_placement_span` has the no-slash branch. Auto-placement
around spans needed three more Chrome behaviours: the occupancy grid tracks
ROW spans, an auto-row item is searched from the sparse-packing cursor (no
back-fill), and items with a definite row and column claim their cells first.
An item spanning explicit rows stretches to the spanned rows.

| case (3 x 100px tracks, 20px gap unless noted) | Chrome 159   | base        | head    |
|------------------------------------------------|--------------|-------------|---------|
| `grid-column:span 2`                           | 0 0 220 10   | 0 0 100 10  | =Chrome |
| next auto item                                 | 240 0 100 10 | 120 0 100 10 | =Chrome |
| `grid-column:span 3` (wraps to row 2)          | 0 10 340 10  | 240 0 100 10 | =Chrome |
| `span 2;margin:10%`                            | 22 22 176 10 | 10 10 80 10 | =Chrome |
| auto item after a full-row span (no back-fill) | 0 20 100 10  | 240 0 100 10 | =Chrome |
| `grid-column:span 2 / 4`                       | 120 20 220 10 | 0 10 100 10 | =Chrome |
| `span 2;padding:10%` (of 220)                  | 0 20 220 44  | 0 10 100 1  | =Chrome |
| `grid-row:span 2`, rows 30px 30px, 2 x 100px   | 0 0 100 60   | 0 0 100 30  | =Chrome |
| third item there                               | 100 30 100 30 | 0 30 100 30 | =Chrome |
| auto item, definite `2 / span 2` item later in source | 100 40 100 20 | 0 20 100 20 | =Chrome |

## 3. `align-items: normal` stretch in an implicit row — OPEN

Tracks 100px 300px, item 1 `padding:11px`, item 2 `padding:6px`, no content:
Chrome item 2 height 22 (stretched to the row), Simple 12. The grid loop only
stretches items in explicit rows (`grid_row < explicit_rows.len()`), because
implicit rows are sized in the same single pass that lays the items out.
Same shape with percent padding: tracks 100px 300px, `padding:10%` and
`padding:5%`: Chrome 30 / 30, Simple 20 / 30 (each its own padding, right;
only the stretch is missing).

## Residue left open by the 2026-11-18 fix

- Percent padding floors to whole px (Chrome keeps 1/64 px): `padding:3.3%`
  of 400 is 13.2 in Chrome, 13 here.
- Paint-side content-box readers still see the authored style (percent
  padding 0): a replaced element's content box, `background-clip` /
  `background-origin: content-box`, an input's text inset. Children and text
  are placed by layout and are right.
- `grid-auto-rows` is not implemented (items in implicit rows are content
  sized); a row-spanning item in implicit rows puts its whole height in its
  first row.
- An auto-width inline-block whose only content is an empty sized box
  shrinks to its padding (px padding too): Chrome 90x50 for `padding:5%`
  around a 50x10 box, Simple 40 wide. Not a percent issue.
- A column flex container with `align-items:flex-start` does not shrink an
  auto-width item (px padding too): Chrome 130, Simple 400.

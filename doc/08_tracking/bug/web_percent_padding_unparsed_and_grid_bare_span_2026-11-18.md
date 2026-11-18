# Web layout: percent padding is not parsed; grid bare `span N` and implicit-row stretch

Found 2026-11-18 while fixing grid item margins (Chrome 159 oracle, 900x2000,
`.g{display:grid;width:400px}`). Gaps 1 and 2 were RESOLVED 2026-11-18 (spec
`test/01_unit/browser_engine/percent_padding_grid_span_chrome159_spec.spl`),
gaps 3 to 7 on 2026-11-19 (spec
`test/01_unit/browser_engine/grid_auto_rows_stretch_paint_padding_chrome159_spec.spl`,
0/31 on base, 31/31 now). The residue is listed at the end.

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

## 3. `align-items: normal` stretch in an implicit row — RESOLVED (2026-11-19)

Was: the grid loop only stretched items in explicit rows
(`grid_row + grid_row_span <= explicit_rows.len()`), because implicit rows
were sized in the same single pass that laid the items out; an item spanning
columns never stretched; `align-items` / `align-self: center | end` did
nothing; a definite-row item laid out before an earlier row grew kept its
stale y; a row-spanning item put its whole height in its first row.

Now (`layout_with_style_flow`, grid branch, `..._layout_engine.spl`): the
first pass places and measures every item and records it; rows are then
finished (spanning items share their deficit equally among the content sized
rows they span, `fr` implicit rows equalize); a second pass re-lays only the
items whose row offset moved, that stretch to a content sized row, or that
are centred / end-aligned. Items in rows that are all FIXED (explicit, or a
`grid-auto-rows` length) still stretch in the first pass.

| case (x y w h in a 400 px container)                         | Chrome 159    | base         | head    |
|--------------------------------------------------------------|---------------|--------------|---------|
| tracks 100px 300px, `padding:10%` beside `padding:5%`        | 0 0 100 30    | 0 0 100 20   | =Chrome |
| tracks 100px 300px, `padding:6px` beside `padding:11px`      | 100 0 300 22  | 100 0 300 12 | =Chrome |
| 2 x 200px, auto item beside `height:40px`                    | 200 0 200 40  | 200 0 200 1  | =Chrome |
| row 2: item with a 10 px child beside `height:20px`          | 0 40 200 20   | 0 40 200 10  | =Chrome |
| `border:3px;padding:2px;margin:5px` beside `height:40px`     | 205 5 190 30  | 205 5 190 10 | =Chrome |
| border-box `padding:5px` item, its `height:50%` child        | 205 5 190 15  | 205 5 190 1  | =Chrome |
| `align-items:center`, `height:10px` beside `height:40px`     | 200 15 200 10 | 200 0 200 10 | =Chrome |
| `grid-column:2;grid-row:2;height:30px` first in source, row 1 is 12 | 100 12 100 30 | 100 0 100 30 | =Chrome |
| `grid-column:span 2` with a 10 px child beside `height:40px` | 100 0 200 40  | 100 0 200 10 | =Chrome |
| `grid-row:span 2;height:60px` beside two `height:10px` items: second item | 200 30 200 10 | 200 60 200 10 | =Chrome |

## 4. `grid-auto-rows` — RESOLVED (2026-11-19)

Was: not parsed; every implicit row was content sized.

Now: `Style.grid_auto_rows` holds the normalized track list
(`normalized_grid_auto_tracks`, `..._declarations.spl`): `<N>px` (px, em,
rem, vw, vh lengths), `auto` (`auto`, `min-content`, `max-content`, a
percentage in an auto-height grid), `<N>auto` (`minmax(<length>, auto)`: a
floor that still grows), `<N>fr`. The list cycles over the implicit rows. A
fixed row never grows with its items and stretches them in the first pass.
Anything else (`minmax(<length>, <length>)`, `fit-content()`, an unknown
token) drops the declaration.

| case                                                          | Chrome 159    | base         | head    |
|---------------------------------------------------------------|---------------|--------------|---------|
| `grid-auto-rows:50px`, 2 x 100px, third (empty) item          | 0 50 100 50   | 0 1 100 1    | =Chrome |
| same, container                                               | 400 x 100     | 400 x 2      | =Chrome |
| `50px` row, item with an 80 px child                          | 0 0 100 50    | 0 0 100 80   | =Chrome |
| `grid-auto-rows:20px 40px`, third row                         | 0 60 400 20   | 0 2 400 1    | =Chrome |
| `grid-template-rows:30px;grid-auto-rows:50px;row-gap:6px`, row 2 | 0 36 200 50 | 0 36 200 1   | =Chrome |
| `minmax(40px,auto)`, row 1 empty / row 2 with a 60 px item    | 40 / 60       | 1 / 60       | =Chrome |
| `grid-row:span 2` in `grid-auto-rows:50px`                    | 0 0 200 100   | 0 0 200 1    | =Chrome |
| `grid-auto-rows:1fr`, rows with 60 px and 20 px content       | 60 / 60       | 60 / 20      | =Chrome |
| `grid-auto-rows:2em;font-size:10px`                           | 0 0 200 20    | 0 0 200 1    | =Chrome |

## 5. Paint-side percent padding — RESOLVED (2026-11-19)

Was: paint reads `styles[i]`, where a percent padding is unresolved (px 0),
so `background-clip` / `background-origin: content-box` covered the padding.

Now: `web_styles_with_painted_percent_padding` (`..._layout_engine.spl`)
returns the styles with each percent padding resolved against the containing
block layout used (parent content width past inline ancestors; parent
padding box for an abspos box; the grid area for a grid item, whose column is
the last track starting at or before its left edge). It is applied once at
the two paint entries: `paint` (`..._paint_raster.spl`, the software raster)
and `_simple_web_layout_compose_retained` (`..._renderer.spl`, the draw-IR
lane: clip cache, visible nodes, commands, input hits). It returns `styles`
itself when no node has a percent padding. The copy is a full
`Style.copy_from`: the layout clone behind `style_with_resolved_percent_padding`
keeps only what layout reads and dropped the top / bottom border colours.

Whole-frame mismatch vs Chrome 159 `--screenshot` (400x160, device scale 1):

| page                                                              | base    | head   |
|-------------------------------------------------------------------|---------|--------|
| `padding:10%;background-clip:content-box`                         | 52.50 % | 0.00 % |
| `padding:10%;background-origin:content-box` no-repeat gradient    | 52.50 % | 0.00 % |
| grid item `padding:10%` (100 px area), `content-box` clip         | 3.75 %  | 0.00 % |
| abspos `padding:10%` (400 px padding box), `content-box` clip     | 17.50 % | 0.00 % |
| border + radial gradient, `content-box` origin and clip           | 59.91 % | 0.00 % |
| same clip on a page WITH text (draw-IR lane)                      | 52.69 % | 0.32 % |

The last row equals its px twin (0.32 %, text antialiasing). The other
paint-side readers (list marker, overflow clip, `<img>` content box,
`text-align:right`) render a percent page pixel-identical to its px twin on
base and head alike: layout already placed them.

## 6. Percent padding is floored — CHANGED to round-to-nearest (2026-11-19)

Chrome keeps 1/64 px and snaps at paint. `padding:1.7% 0.4%` of 333 around a
10 px child: Chrome child at y 5.656 (painted on row 6), box height 21.3125.
Base (floor): y 5, height 20. Head (round): y 6, height 22. Each edge is now
within 0.5 px instead of 1. Not fractional layout: that stays open.

## 7. A resolved percent dropped the Grid fields — RESOLVED (2026-11-19)

`style_with_width` (the clone behind `style_with_resolved_percent_padding`,
`..._percent_margins` and `..._percent_min_max`) did not copy the Grid fields,
so a grid container with `padding:5%` or `max-width:75%` was laid out as a
block (children 360 px wide and stacked; Chrome 100 px side by side). It now
restores them, as `style_with_height` already did.

## Residue still open

- `grid-auto-columns` and implicit columns: `grid-auto-flow:column;
  grid-auto-columns:100px` with no template is a block here (three stacked
  400 px rows; Chrome three 100 px columns); with `grid-template-columns:100px`
  the second and third item go to rows 2 and 3 (Chrome: 50 px columns).
- An empty auto-height block is 1 px high (Chrome 0), so an empty
  `align-self:start` grid item is 1 px.
- Fractional layout units (sub-px padding, 1/64 px in Chrome).
- A percent `margin-top` on a grid container inside a flow root is not
  applied (Chrome 20 px for 5% of 400).
- `<textarea style="padding:10%;width:100px;height:40px">`: Chrome 100x80,
  here 180x120.
- px padding too (not a percent issue): an `<input>` with `padding-left`
  paints its background only `width` wide (layout box is right); a flex
  item's `background-clip:content-box` paints the whole border box on a page
  routed through the draw-IR lane.
- `minmax(<length>, <length>)` and `fit-content()` in `grid-auto-rows`.
- An auto-width inline-block whose only content is an empty sized box
  shrinks to its padding (px padding too): Chrome 90x50 for `padding:5%`
  around a 50x10 box, Simple 40 wide. Not a percent issue.
- A column flex container with `align-items:flex-start` does not shrink an
  auto-width item (px padding too): Chrome 130, Simple 400.

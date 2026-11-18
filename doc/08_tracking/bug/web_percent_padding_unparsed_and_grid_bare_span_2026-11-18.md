# Web layout: percent padding is not parsed; grid bare `span N` and implicit-row stretch

Found 2026-11-18 while fixing grid item margins (Chrome 159 oracle, 900x2000,
`.g{display:grid;width:400px}`). Three gaps left open, each measured.

## 1. Percent padding is dropped engine-wide

`_padding_length_px` (`simple_web_html_layout_renderer_declarations.spl`)
accepts px, 0, em, rem, vw, vh. A `%` token returns -1, which drops the whole
`padding` declaration, in every layout context (not only grid).

| case (tracks 100px 300px)            | Chrome 159      | Simple        |
|--------------------------------------|-----------------|---------------|
| item 1 `padding:10%` (x y w h)       | 0 0 100 30      | 0 0 100 1     |
| item 2 `padding:5%`                  | 100 0 300 30    | 100 0 300 1   |
| item 1 `padding-top:25%;height:10px` | 0 0 100 35      | 0 0 100 10    |

Fix shape: a percent encoding on `Style.pad_*` (like the negative
`margin_t_milli`), resolved against the containing block width in each layout
path; a grid item resolves against its grid area width.

## 2. Bare `grid-column: span N`

`normalized_grid_placement` requires a positive start line, so `span 2`
normalizes to "" and the item is one track wide. Chrome, 3 x 100px tracks with
20px gap, `grid-column:span 2;margin:10%`: 22 22 176 10. Simple: 10 10 80 10.
`1 / span 2` works. `grid_placement_span` needs the same no-slash branch.

## 3. `align-items: normal` stretch in an implicit row

Tracks 100px 300px, item 1 `padding:11px`, item 2 `padding:6px`, no content:
Chrome item 2 height 22 (stretched to the row), Simple 12. The grid loop only
stretches items in explicit rows (`grid_row < explicit_rows.len()`), because
implicit rows are sized in the same single pass that lays the items out.

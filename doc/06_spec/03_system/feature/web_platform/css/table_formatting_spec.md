# Fixed HTML table formatting

This bounded conformance slice proves fixed direct and row-grouped HTML tables
through the shared Style, canonical table owner, Draw IR, and Engine2D paths.

## Fixed table scenario

1. Render a 40-pixel `table-layout: fixed` table with a caption, two rows,
   two columns, padded bordered cells, and one `colspan="2"` cell.
2. Require computed display roles: `table`, `table-caption`, `table-row`, and
   `table-cell`.
3. Require exact caption, row, and cell geometry plus Draw IR parentage.
4. Require absolute Engine2D pixels for the caption, each cell background,
   a cell border, and the canvas below the table.

## Grouped tbody control

1. Render two fixed rows inside a `tbody`.
2. Require the `table-row-group` computed role and exact row/cell geometry.
3. Require canonical Draw IR parentage from table to group to row to cell.
4. Check absolute Engine2D cell pixels only after semantics and Draw IR pass.

This slice intentionally does not claim the automatic table layout algorithm,
rowspan placement, or collapsed-border conflict resolution. Those remain
explicit unsupported gaps.

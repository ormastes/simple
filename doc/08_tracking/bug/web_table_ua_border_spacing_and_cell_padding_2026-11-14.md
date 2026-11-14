# Web renderer: unstyled tables had no UA border-spacing and no cell padding

Found 2026-11-14 by the combination matrix
(`sh scripts/check/check-web-combo-matrix-chrome.shs`, Chrome 159.0.8154.6).
Status: FIXED; 26 matrix cells (116 element ids) left the ratchet baseline.

Chrome's UA stylesheet has `table { border-spacing: 2px }` and
`td, th { padding: 1px }`. `_tag_defaults_without_metadata`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`)
set only `display` for those tags.

| `<table>` of 3x2 text cells | Chrome | Simple before |
|---|---|---|
| table box | 67x58 | 54x48 |
| first cell | 2,2 20x26 | 0,0 18x24 |
| second-row middle cell | 24,30 20x26 | 18,24 18x24 |

Fix: the two defaults in the tag-defaults function, plus an effective spacing
of 0 under `border-collapse: collapse` in the table branch of
`simple_web_html_layout_renderer_layout_engine.spl` (border-spacing does not
apply in the collapsing model; with a non-zero default it has to be said).

Specs: `test/01_unit/browser_engine/table_ua_cell_padding_and_spacing_spec.spl`
(reproduction: the plain 3x2 table; generalization: `border-collapse:collapse`,
authored `border-spacing:0` + `padding:0`, a `width:200px` table).
Red (6 of 6 failing) -> green (6 of 6 passing).

## Residuals this exposed (open)

- **Whole-pixel column widths.** Chrome's cells are 19.8 px wide, Simple's 20:
  the plain table is 68 px wide where Chrome reports 67, and a `width:200px`
  two-cell table splits 100/94 where Chrome splits 99/95. Within the matrix's
  1 px tolerance. Chrome-exact assertions are kept RED in
  `test/01_unit/browser_engine/table_fractional_column_width_spec.spl`
  (`# @tag:in-development`, 2 of 2 failing). Where: column widths are whole
  `i32` pixels in `explicit_auto_table_column_offsets`
  (`simple_web_html_layout_renderer_layout_foundation.spl:1550`). Unblock:
  size table columns in sub-pixel units and round only the final box edges;
  then delete the tag line from that spec.
- **A cell's max-content width drops the spaces around an inline child.**
  `<td>ab <span>cd</span> ef</td>`: Chrome 59 px, Simple 50 px (two spaces).
  9 `tt-td-*` matrix cells.
- **`cellspacing` / `cellpadding` attributes are ignored — and `=0` now shows.**
  They were ignored before this change too, but with defaults of 0 a table
  written `cellspacing="0" cellpadding="0"` happened to match Chrome; it is
  now 2 px / 1 px off. `<table cellspacing="0" cellpadding="4">` of two
  cells: Chrome 51x32. No HTML fixture or catalog page in the repo uses either
  attribute (checked `examples/` and `test/fixtures/`). Where:
  `presentational_attr_decls` and its `html_has_presentational_attr` precheck
  know neither name; `cellpadding` also needs the cell to see its table.
- **A `td` whose `display` is not `table-cell` is not laid out.**
  `<td style="display:block">` (also `inline`, `inline-block`, `flex`, `grid`)
  between two ordinary cells: Chrome 24,2 19x26 inside a 67 px table; Simple
  gives the cell a 0x0 box at the page origin and stretches the table to its
  container. 8 `tc-td-d-*` / related matrix cells.

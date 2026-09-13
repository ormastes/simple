# `<table>` is laid out as a full-width block: no shrink-to-fit, no UA `border-spacing: 2px`, no `<th>` defaults

- Status: OPEN — located, not fixed (round 5 spent its oracle budget on the
  paint/layout advance parity regression; see "Why round 5 did not fix it")
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
  (the `display == "table"` branch, :1659-1850), plus the UA defaults in
  `..._declarations.spl` and `..._style.spl`

## Symptom, against a Chrome oracle

Probe `test/fixtures/browser_engine/layout/round4_probe.html` at 900x20000,
`body{margin:0;font:16px/1.5 sans-serif}`, harvested with headless Chrome
`--dump-dom` + `getBoundingClientRect()`:

| element | Chrome | Simple |
|---|---|---|
| `table#t1` | 119 x 30 | **900 x 48** |
| `td#d1` / `td#d2` | side by side | full-width stacked blocks |

## What IS already implemented (do not rewrite it)

The auto-table machinery exists and is not a stub: `explicit_auto_table_column_offsets`
is called at :1659-1668 with the shrink-to-fit intent already stated in its own
comment ("width:auto tables shrink to fit: pass 0 as the available inner width so
no leftover space is distributed across the columns"), and the branch below it
(:1670-1850) implements per-row placement, `border-spacing` x/y, and a
`border-collapse` half-border slice with its limits documented inline. The UA
display mapping is also present: `..._declarations.spl:1410-1420` maps `table`
-> `display: table`, `tr` -> `table-row`, `td`/`th` -> `table-cell`.

## Where it actually breaks, stated as located-but-unverified

Two independent gaps, both read off the source rather than measured (round 5 had
no spare binary time to instrument them — treat as the next investigator's
starting points, not as findings):

1. **The whole table branch is gated behind
   `auto_column_offsets.len() > 0 or st.border_spacing_x_px > 0 or
   st.border_spacing_y_px > 0 or table_layout == "fixed"` (:1671-1678).**
   `border_spacing_{x,y}_px` default to **0** (`..._style.spl:610`), but Chrome's
   UA sheet gives `table { border-spacing: 2px }`. So on a plain `<table>` with no
   author CSS the only thing that can open the branch is a non-empty
   `explicit_auto_table_column_offsets`, and the observed full-width stacked cells
   say it came back empty. Fixing the UA default alone would open the branch —
   and is independently correct, since Chrome's 119 = content + 3 x 2 px spacing
   + borders.
2. **The table's own BOX is never shrunk.** Sizing happens earlier, at
   `var node_w = if st.width_px > 0: explicit_node_w else: w` (:1561). A
   `width: auto` table takes the full containing width like any block, so even
   with correct column offsets the `<table>` element itself stays 900 px. CSS
   2.1 §17.5.2 shrink-to-fit — `min(max(preferred-minimum, available),
   preferred)` over the column max-content widths — has no implementation on
   this path.

Also missing, smaller: `<th>` has no UA `font-weight: bold` /
`text-align: center`, and row height is not `max(cell content) + padding`.

## Why round 5 did not fix it

Round 5's brief carried four targets. Target 1 (paint and layout measuring an
inline run with different advances — a *measured* pixel regression on
`forms-media`) was the only one with a regression attached, and on this host one
full pass of `check-chrome-catalog-pixel-diff.shs` is ~1 h wall (8 pages, a
headless Chrome render and an interpreter-mode Simple render each), run strictly
one at a time. Table geometry changes the box tree on any page containing a
table, so it needs its own full pass. Doing both on one budget would have meant
landing at least one of them unmeasured, which is how the round-4 `forms-media`
regression got in.

## What would close it

Both gaps together, in one change, with a fresh 8-page pixel table: the UA
`border-spacing: 2px` default; shrink-to-fit at the `display == "table"` sizing
site; `th` bold + centred; row height from max cell content. The probe's
acceptance figure is `table#t1` 119 x 30 (+/-1 px), with `d1`/`d2` side by side.

## Round 8 (2026-09-13) — automatic column sizing landed; catalog probes deferred

CSS 2.1 §17.5.2.2 automatic column distribution is now implemented once, as a
pure function, and consumed by both table lanes:

- `src/lib/gc_async_mut/gpu/browser_engine/layout_table.spl:203`
  `table_distribute_auto_columns(col_min, col_max, available)`.
- `layout_table.spl:378` `layout_table(node, ctx)` — the M14 spec-facing lane,
  which previously did not exist at all (`table_layout_spec` was 0/7 because the
  symbol it imports was absent, not because the numbers were wrong).
- `simple_web_html_layout_renderer_layout.spl:1129`
  `table_cell_max_content_width`, replacing the `return []` bail that sent every
  table whose cells state no `width` out of the automatic path and into an equal
  split, and the `1` px placeholder for auto cells.

`test/01_unit/browser_engine/table_layout_spec.spl` is 9/9 (7 original + 2 that
actually discriminate content sizing from an equal split; a sabotage of the
distributor reddens exactly those 2).

**Still open from this record:** `rowspan`, `border-collapse` winner widths,
percentage column widths, and the catalog-page table probes. The probes were
deliberately NOT added: they change the catalog pages, which invalidates the
committed Chrome reference geometry, and Chrome's own capture times out on the
macOS host used for round 8 — so the reference could not be regenerated
honestly in the same round. Adding probes must be paired with a fresh reference
capture on a host where Chrome completes.

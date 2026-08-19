# browser_engine: table layout stacks rows/cells vertically as blocks (no columns, no shrink-to-fit)

- **Date:** 2026-08-19
- **Status:** FIXED (2026-08-19, same day)
- **Severity:** medium (layout correctness vs Chrome oracle)
- **Module:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl` (the `layout()` pipeline used by the component-diff harness and BrowserSession rendering)

## Symptom

A minimal 2x3 table (`tools/component_diff/fixtures/table.html`, explicit
`<tbody>`, `border-collapse: collapse`, fixed 60px cells) lays out with every
`<td>` stacked VERTICALLY at full container width, and `<tr>`/`<table>`
expanded to the body width (780px) instead of shrink-to-fit.

Measured (Chrome for Testing 151.0.7922.34 vs `bin/simple run` extraction,
evidence `tools/component_diff/out/table/table.state0.diff.txt`):

| node | Chrome | Simple |
|---|---|---|
| `#t` | `[10,10 196x51]` | `[10,10 780x156]` |
| `#r0` | `[11,11 195x25]` | `[10,10 780x78]` |
| `#c00` | `[11,11 65x25]` | `[10,10 66x26]` |
| `#c01` | `[76,11 65x25]` (beside c00) | `[10,36 66x26]` (BELOW c00) |

All 18 node lines diverge (`divergent_s0=36` diff lines) — this is a
structural table-layout gap, not a pixel-rounding class.

## Analysis

`tr`/`td` are treated as ordinary block boxes: no row formatting context, no
column x-advance, no table shrink-to-fit width, no border-collapse. A
`layout_table.spl` module exists in the browser_engine directory (M14 layout
family) but the `simple_web_html_layout_renderer` pipeline that
`parse_html → compute_styles → layout` drives does not route table display
types to it. Not cheap to fix (needs a table formatting context in the
renderer's layout pass), hence recorded rather than patched inline.

## Reproduce

```sh
sh tools/component_diff/run_component_diff.shs --component table
cat tools/component_diff/out/table/table.state0.diff.txt
```

Pinned fail-closed (may shrink, must not grow: `divergent_s0<=36`) in
`test/03_system/browser_engine/chrome_component_set_spec.spl`.

## Fix (2026-08-19)

Root cause: the table branch in
`simple_web_html_layout_renderer_layout.spl` existed but was gated on
`table_layout == "fixed"` OR authored `border-spacing` OR an explicit table
`width` (auto column offsets required `st.width_px > 0`). The fixture class —
`table-layout: auto`, `border-collapse: collapse`, width:auto table with
explicit cell widths — failed all three admissions, and the collapse resolver's
bounded slice (1 row x 2 cells) left spacing untouched, so the table fell into
the block fallback: stacked full-width td/tr.

Changes (all in `simple_web_html_layout_renderer_layout.spl`):
1. `explicit_auto_table_column_offsets` is now computed for ALL auto-layout
   tables; a width:auto table passes 0 available width so no leftover space is
   distributed — columns shrink to their explicit cell widths (offsets still
   return `[]`, preserving the block fallback, when any column lacks an
   explicit width under zero spacing).
2. Shrink-to-fit: a width:auto table's own box narrows to
   grid + padding + border (+ collapse outer half-border) instead of filling
   the containing block.
3. border-collapse geometry, uniform-border slice (limits stated in code):
   each column track carries `(border_l+border_r)/2` less than the separate
   model, the grid origin shifts by the round-half-up outer half-border, and
   each row sheds `(border_t+border_b)/2`. Non-uniform winner widths and
   row/col spans keep the separate-model geometry.

Result: `divergent_s0` 36 -> 14; `#t`, `#tbody`, both `#r*`, and all six
`#c*` boxes now match Chrome EXACTLY (e.g. `#c01 [76,11 65x25]`). The
residual 14 lines are 6 text-node pairs (font advance / line-height metrics,
a pre-existing divergence class shared with the counter component) plus
`body` (Chrome collapses the table's margin through the body). Pin lowered
shrink-only to `divergent_s0<=14` in `chrome_component_set_spec.spl`.

Regression evidence (2026-08-19, deployed fixed seed, SIMPLE_TIMEOUT_SECONDS=3600):
`chrome_component_set_spec` 6/6, `chrome_counter_component_spec` 5/5 (counter
divergence unchanged at 24), `chrome_layout_differential_spec` 4/4 (pure block
layout still byte-exact vs Chrome), `chrome_paint_differential_spec` 4/4,
`chrome_composite_differential_spec` 3/3, `engine2d_drawing_spec` 2/2,
`layout_box_content_contract_spec` 6/6, vector-font 2/2, sandbox 1/1 — all
after refreshing each lane's retained evidence (concurrent lanes touch the
shared tool files, which staleness-gates other components' evidence).
`docker_vulkan_browser_spec` needs a Vulkan container and fails identically
with and without this change (environment-gated). `simple_web_css_cascade_spec`
(8/11) and `simple_web_layout_child_index_spec` (21/22) carry pre-existing
failures on this worktree: re-run with this fix reverted to committed content
produced IDENTICAL counts, and neither spec exercises table layout.

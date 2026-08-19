# browser_engine: table layout stacks rows/cells vertically as blocks (no columns, no shrink-to-fit)

- **Date:** 2026-08-19
- **Status:** OPEN
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

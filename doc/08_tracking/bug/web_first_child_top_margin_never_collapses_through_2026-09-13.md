# Web renderer: a first child's TOP margin never collapses through its block

- status: OPEN
- area: lib / browser_engine layout
- found: 2026-09-13, Chrome parity round 6
- file: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`

## Symptom

CSS 2.2 §8.3.1 collapses a block's top margin with its FIRST in-flow child's
top margin when no border or top padding separates them. The Simple web
renderer keeps the child's top margin inside the parent's content height, so
every such block is ~16 px taller than Chrome and everything below it shifts.

Chrome oracle (headless, 900x20000, `body{margin:0;font:16px/1.5 sans-serif}`,
`*{box-sizing:border-box}`) vs Simple, height in px:

| fixture | Chrome | Simple |
|---|---|---|
| `<div style="padding-bottom:10px"><p>t</p></div>` | 50 | 66 |
| `<div style="border-bottom:2px solid #000"><p>t</p></div>` | 42 | 58 |
| `<div><p>t</p></div>` | 24 | 40 |
| `<div style="height:70px"><p>t</p></div>` | 70 | 70 (ok) |
| `<div style="overflow:hidden"><p>t</p></div>` | 56 | 56 (ok — BFC, no collapse) |

The last two are correct and are pinned as AC-5/AC-6 of
`test/01_unit/browser_engine/li_last_child_margin_collapse_spec.spl`.

## Why the round-6 bottom-margin fix did not cover it

The BOTTOM half is now fixed: `block_bottom_margin_collapses_through` +
`LayoutResult.trailing_margin_b` let the last child's bottom margin leave the
box and re-appear between the block and its next sibling. That works because
the margin is known AFTER the children are laid out.

The TOP half cannot use the same shape. The caller computes
`collapsed_margin = collapse_margins_signed(prev_margin_b, cst.margin_t)` and
advances `cy` BEFORE `layout_with_style` runs, so the first child's top margin
is not yet known at the moment the parent's box origin is fixed. Closing it
needs either a pre-pass that resolves a subtree's leading margin, or a
two-phase placement that re-offsets the parent subtree once the first child is
measured (`offset_layout_subtree` already exists for that mechanics).

The `body` special case in the same loop (`child_count == 0 and
nodes[i].tag == "body"`) is a hand-rolled instance of exactly this rule for one
tag; generalising it is the work.

## Repro

    SIMPLE_2D_BACKEND=cpu_simd SIMPLE_EXECUTION_MODE=interpreter \
      build/cargo-r2/release/simple run \
      test/01_unit/browser_engine/li_last_child_margin_collapse_spec.spl

and add the three rows above as expectations; they fail by exactly 16 px.

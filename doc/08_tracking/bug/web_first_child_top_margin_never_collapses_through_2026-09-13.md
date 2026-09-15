# Web renderer: a first child's TOP margin never collapses through its block

- status: FIXED 2026-09-13 (Chrome parity round 7)
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

## Fix (round 7, 2026-09-13)

`LayoutResult` gains `leading_margin_t`, the exact mirror of the round-6
`trailing_margin_b`, and `block_top_margin_collapses_through` mirrors
`block_bottom_margin_collapses_through`'s exclusion set (documents, non-block
display, out-of-flow, floats, BFC roots, widget panels, flex/grid items, and —
conservatively — every height clamp).

The chicken-and-egg the record identified is resolved with the two-phase
mechanics `offset_layout_subtree` already serves elsewhere, not with a pre-pass:
the block child is laid out at the advance computed from its DECLARED
margin-top, and immediately afterwards the caller recomputes the advance from
the child's EFFECTIVE top margin (`collapse_margins_signed(declared,
child.leading_margin_t)`) and translates the child subtree by the difference.
When this block itself collapses its top through, the whole effective margin is
pulled back out (`corrected_top_advance = 0`), `cy` un-advances, the height
shrinks by it, and the margin is returned as this block's `leading_margin_t` for
its own parent to collapse — so nesting N wrappers still yields ONE margin.
The `<body>` hand-rolled case in the same loop is kept and now uses the
effective margin too.

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
— `LayoutResult.leading_margin_t` (:173), `block_top_margin_collapses_through`
(after `offset_layout_subtree`), the correction block in the block child loop.

## Specs (both required by .claude/rules/testing.md)

- Reproducing: `test/01_unit/browser_engine/first_child_top_margin_collapse_spec.spl`
  AC-1..AC-3 are the three rows of the symptom table above (24 / 50 / 42).
- Generalization (same file, adjacent paths): AC-4..AC-6 pin the cases that must
  NOT collapse (top padding, `overflow:hidden` BFC, explicit height), AC-7 pins
  that the escaped margin still separates the block from what precedes it, AC-8
  pins that two nested wrappers yield ONE margin rather than one per level,
  **AC-9** pins a `<li>` — whose synthesised `::marker` is its first NODE, so a
  block loop that counted it could never let the real first child's margin
  escape — and **AC-10** pins that an out-of-flow (absolutely positioned) first
  child does not donate its margin to the block.

Sabotage triple: with `block_top_margin_collapses_through` forced to `false`,
AC-1/2/3/8 fail and AC-4/5/6/7 still pass; restored, 10/10 pass. The round-6
trailing-half spec `li_last_child_margin_collapse_spec.spl` stays 12/12.

## Known limit left open by the round-7 fix

The escape is computed for the FIRST in-flow child only. A first child that is
itself **self-collapsing** (an empty block whose own top and bottom margins
collapse into one, handled by the `self_collapsing` branch in the same loop)
forwards its collapsed margin to the next sibling through `prev_margin_b`, and
that sibling is no longer `child_count == 0`, so its margin is placed inside the
block rather than joining the escape. Closing it needs an "still at the block's
top edge" flag carried across self-collapsing children rather than a
`child_count == 0` test. Not probed against a Chrome oracle in round 7 — stated
as the next thing to measure, not as a measured defect.

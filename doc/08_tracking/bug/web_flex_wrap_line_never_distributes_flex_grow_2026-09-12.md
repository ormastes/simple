# A wrapping flex line never distributes free space to `flex-grow`

- Status: FIXED 2026-09-12
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
- Found by: `scripts/check/check-chrome-layout-geometry-diff.shs` at `GEOM_DIFF_HEIGHT=20000`
- Spec: `test/01_unit/browser_engine/flex_wrap_grow_distribution_spec.spl`

## Symptom

The catalog's `.flex` row holds two `.card { flex: 1 1 180px }` items. Measured
against Chrome 152 headless at 900 px:

| element | Chrome (x,y,w,h) | Simple before | Simple after |
|---|---|---|---|
| `div.flex` | 0, 0, 900, 48 | 0, 0, 900, 48 | 0, 0, 900, 48 |
| card 1 | 0, 0, **444**, 48 | 0, 0, **180**, 48 | 0, 0, 444, 48 |
| card 2 | **456**, 0, **444**, 48 | **192**, 0, **180**, 48 | 456, 0, 444, 48 |

Both the 264 px width shortfall and the 264 px displacement of the second card
are one cause. F22 ranked this class third (12 root mismatches at 760 px).

## Root cause

The `flex_wrap != "nowrap"` branch of the row-flex layout computes
`base_w_wrap` — the item's flex BASIS — and passes it straight to
`layout_with_style` as the item width. Nothing ever grows it. The line's free
space (`iw - line_widths[line]`) was handed entirely to `row_flex_distribution`
for `justify-content`.

That is backwards per CSS Flexbox SS9.7 ("Resolving Flexible Lengths"):
flexible lengths resolve FIRST, and a line whose `flex-grow` factors sum to a
positive number therefore has **no** free space left for `justify-content`.
Note this is not the same defect as the one F20 fixed
(`flex_wrap_auto_base_width`, which sizes an item that states *nothing*); that
helper deliberately returns the caller's base width when `flex_grow != 0`,
precisely because growth was supposed to be handled here.

The non-wrapping branch was never affected — it already called
`row_flex_distribution` with a grow-aware path.

## Fix

- The measure pass accumulates `line_grow_totals[line]`, the sum of `flex-grow`
  over the items on each wrapped line.
- The placement pass grows each item by the **prefix difference** of the line's
  free space, `floor(free*acc_after/total) - floor(free*acc_before/total)`, so
  integer division loses no pixel: the line's items sum to exactly the free
  space regardless of how many items or how uneven the factors.
- `row_flex_distribution` is called with `0` free space on any line whose grow
  total is positive, so `justify-content` no longer double-spends space that
  growth already consumed.

## Sabotage triple

Measured 2026-09-12 on `build/cargo-r2/release/simple` (39178424 1789197971).

1. Baseline: `4 examples, 0 failures`.
2. Neutralise only `base_w_wrap = base_w_wrap + grow_after - grow_before`
   (multiply the delta by 0). `4 examples, 3 failures`, verbatim:
   - `AC-1 ... expected 180 to equal 444` (the item stays at its flex basis)
   - `AC-2` fails (the item IS 180)
   - `AC-3 ... expected 192 to equal 456` (the second card is displaced by the
     same 264 px)
   AC-4 still passes — the items were always on one line; only their size was
   wrong, which is exactly the defect's shape.
3. Restore: `4 examples, 0 failures`.

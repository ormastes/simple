# `<sub>`/`<sup>` line box is the inline's own height, and the obvious strut fix contradicts Chrome (2026-09-14)

Status: OPEN, and deliberately NOT fixed. Round 23 of the web↔Chrome
layout-geometry parity arc attempted it, measured a contradiction, and backed
the change out rather than tune it to one context.

## Symptom

A block whose only inline child is a `<sub>` or `<sup>` gets the CHILD's line
height, not the line's.

Catalog `html.html`, `path:0/0/4/2/70/1` (the `html:sub` sample's
`div.feature-example`):

| | Chrome | Simple |
|---|---|---|
| `<div>` | 106,8303 728x**27** | 106,8275 728x**13** |
| `<sub>` | 106,8312 76x15 | 106,8279 74x13 |

The enclosing `<li>` is 14 px short as a result (Chrome 91, Simple 77), and the
same shape repeats for `<sup>` at `li` 72. Together ~714 Σ attributed.

## Mechanism (this part is certain)

`inline_line_h` is seeded from the FIRST CHILD's style
(`simple_web_html_layout_renderer_layout.spl:3680`,
`inline_line_h = style_line_h(cst)`), and
`align_inline_line_baselines` (`:274`) — which DOES restore the strut from
`line_style` — returns `line_height` untouched when its node list is empty.
`vertical-align: sub`/`super` is not `baseline`, so such a child is never pushed
onto `inline_baseline_nodes` and the list IS empty. A `<small>` in the same
position is baseline-aligned, goes through the strut path, and is already
correct — which is the control that isolates this.

## Why the obvious fix was backed out

Seeding from the CONTAINER (`style_line_h(st)`) is what CSS 2.1 10.8.1 says and
it fixes the catalog. Harvested from Chrome 152 `--headless=new
--window-size=900,20000`, a `<div>` containing only a `<sub>`:

| block line-height | strut would be | Chrome measures |
|---|---|---|
| `normal` (no author CSS), 16 px font | 18 | **21** |
| `font: 16px/1.5` (number, inherited) | 24 | **20** |
| `line-height: 24px` (absolute, the catalog) | 24 | **27** |

Row 2 is smaller than its own strut. No "line box contains the strut" rule
produces 20 there. So the strut seed is right in rows 1 and 3 and wrong in row
2, which is a compensating-error state: it would have landed the catalog green
on a rule that cannot be stated. Reverted.

The `<small>` control in the same three contexts gives 18 / 20 / (not measured),
i.e. it tracks the INLINE's line-height in row 2 as well — so whatever Blink is
doing, it is not simply ignoring `<sub>`.

## Measured baseline-shift extension, for whoever takes this

Chrome's line box extends BEYOND the strut when a sub/sup is present. Two font
sizes, `line-height: normal`:

| font-size | strut (`<small>` control) | `<sub>` div | extension |
|---|---|---|---|
| 16 px | 18 | 21 | +3 |
| 32 px | 37 | 43 | +6 |

so the sub extension is linear at `3 × font-size / 16`. `<sup>` measured +4 at
16 px only; the second font size was NOT measured, and the round-23 lane
declined to fit a formula to a single point. Note this is a different quantity
from `baseline_shift = st.font_size / 4` at `..._layout.spl:3800`, which offsets
the child's `y` and is not applied to the line height.

## What a real fix needs

1. A statable rule that produces 21 / 20 / 27 for the three contexts above —
   most likely an ascent+descent (half-leading) model rather than a max of
   line-heights, since the number-vs-absolute `line-height` distinction is what
   separates rows 2 and 3.
2. `<sup>` measured at a second font size before any constant is written.
3. `<small>` kept as the 0-delta control in every context.

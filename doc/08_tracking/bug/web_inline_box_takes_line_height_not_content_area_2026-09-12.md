# An inline element's box is the whole line box, not its font content area

- Status: FIXED 2026-09-12 (vertical geometry only — see "Still open" below)
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
- Found by: `scripts/check/check-chrome-layout-geometry-diff.shs` at `GEOM_DIFF_HEIGHT=20000`
- Spec: `test/01_unit/browser_engine/inline_content_area_half_leading_spec.spl`

## Symptom

Every `<strong>` / `<em>` / `<code>` / `<mark>` / `<a>` in the catalog measured
6 px too tall and 3-4 px too high. On `overview.html` this was the ENTIRE
remaining mismatch set (5 of 5 rows) after F20's round-2 fixes, and the same
class accounted for 51-61 `inline` rows on each of the html / css-layout /
css-paint pages.

Measured on `<p>Paragraph with <strong>…` at 900 px, font `16px/1.5`:

| element | Chrome (y,h) | Simple before | Simple after |
|---|---|---|---|
| `p` (line box) | 274, 24 | 274, 24 | 274, 24 |
| `strong` | **277**, **18** | **274**, **24** | 277, 18 |
| `em` | 277, 18 | 274, 24 | 277, 18 |
| `a` | 277, 18 | 274, 24 | 277, 18 |

Geometry-differ rows for overview went from `dy 4, dh 6` on all five elements to
`dy ≤ 1, dh ≤ 1`.

## Root cause

Two halves of the same misreading of CSS 2.1 SS10.6.1:

1. **Height.** The inline branch left `out_bh[c]` at whatever
   `layout_with_style` produced — the line-height. `line-height` sizes the LINE
   box; the inline box inside it is the font's *content area* (ascent +
   descent). A pre-existing `out_bh[c] = out_bh[c] - 1` hack existed for `span`
   only, which was this bug's symptom being shaved by one pixel for one tag.
2. **Position.** `align_inline_line_baselines` placed every baseline-aligned
   participant at `line_y + ascent - node_baseline_offset`. For an inline
   element both terms are `inline_line_strut_baseline_offset`, so the box
   landed exactly at `line_y` — the line's top edge. An inline box is centred
   in the line box by **half-leading**, `(line_h - content_h) / 2`.

## Fix

- `inline_content_area_height(st)` = `font_size * 9 / 8` (18 px at 16 px), the
  normal-metrics approximation this renderer already uses for vertical font
  geometry. Chrome measures 18 px for the sans stack and 19 px for the
  monospace `<code>` stack; both are inside the differ's 1 px tolerance. A real
  per-family ascent+descent would need font metrics this layout path does not
  carry, and is not invented here.
- An inline element whose laid-out height fits within one line-height takes that
  content-area height. A taller box genuinely wrapped and keeps layout's height.
  The `span`-only `- 1` hack is deleted, superseded by the general rule.
- `align_inline_line_baselines` places a baseline-aligned inline element at
  `line_y + (resolved_height - bh) / 2`.

## Scope limit that is deliberate, not an oversight

Half-leading is applied only when `resolved_height <= style_line_h(line_style)`
— a SINGLE-line run. This renderer models a wrapped `#text` as one tall box
rather than N line boxes, so on a wrapped run `resolved_height` is N
line-heights and centring in it pushes the element down by (N-1)/2 lines.
Measured on a 3-line `<li>`: centring put the `<code>` 12 px too low, worse than
before. Those runs keep the existing top placement until wrapped text is modelled
as real line boxes.

## Still open (NOT fixed here)

The horizontal deltas on the same elements are untouched and are a different
cause — font advance metrics, not flow. On overview Simple places `<strong>` at
x=140 where Chrome has 113 (Simple over-measures the preceding plain text) while
making the bold run itself 43 px against Chrome's 51 (Simple does not apply bold
metrics). Filed separately:
`doc/08_tracking/bug/web_inline_run_x_advance_font_metrics_2026-09-12.md`.

## Sabotage triple

Measured 2026-09-12 on `build/cargo-r2/release/simple` (39178424 1789197971).

1. Baseline: `4 examples, 0 failures`.
2. Force `node_is_half_leaded` to `false` (replace its `display == "inline"`
   term with `false`), leaving the height half of the fix in place.
   `4 examples, 2 failures`, verbatim:
   - `AC-3 ... expected 0 to equal 3` — the element is back on the line's top edge
   - `AC-4` fails (its y equals the paragraph's y again)
   AC-1 and AC-2 still pass, which is the point of splitting the two halves:
   the height rule and the placement rule are independently load-bearing.
3. Restore: `4 examples, 0 failures`.

Regression check on the two specs F20 landed over the same code —
`flex_wrap_auto_width_item_spec.spl` and `form_control_ua_font_spec.spl` —
both `4 examples, 0 failures` after this change.

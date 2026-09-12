# `grid-template-columns: repeat(N, minmax(a, b))` silently lays out as a block

- Status: FIXED 2026-09-12
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`
- Found by: `scripts/check/check-chrome-layout-geometry-diff.shs` at `GEOM_DIFF_HEIGHT=20000`
- Spec: `test/01_unit/browser_engine/grid_repeat_minmax_track_list_spec.spl`

## Symptom

On `examples/06_io/ui/web_catalog/css-layout.html`, the `.grid` container
(`grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 12px`) laid out as
three full-width stacked rows instead of one three-column row. Measured against
Chrome 152 headless at 900 px:

| element | Chrome (x,y,w,h) | Simple before | Simple after |
|---|---|---|---|
| `div.grid` | 0, 48, 900, **48** | 0, 48, 900, **168** | 0, 48, 900, 48 |
| card 1 | **0**, 48, **292**, 48 | 0, 48, **900**, 48 | 0, 48, 292, 48 |
| card 2 | **304**, 48, **292**, 48 | **0**, **108**, **900**, 48 | 304, 48, 292, 48 |
| card 3 | **608**, 48, **292**, 48 | **0**, **168**, **900**, 48 | 608, 48, 292, 48 |

The +120 px the container gained then shifted **every** element below it on the
page, so a single declaration-parsing gap accounted for a large share of that
page's `block-flow` mismatch rows.

## Root cause

`normalized_grid_track_list` (`..._declarations.spl`) splits the raw declaration
on spaces and requires every token to end in `fr` or `px`. `repeat(3, minmax(0,
1fr))` splits into `repeat(3,`, `minmax(0,` and `1fr))` — none matches, so the
function returns `""` and `st.grid_template_columns` is never set.

Layout gates its grid branch on `st.display == "grid" and
grid_columns.len() > 0` (`..._layout.spl:1803`). An unset track list therefore
does not produce a degraded grid; it produces **no grid at all** — the container
falls through to block layout, which is why the failure is silent and looks like
a vertical-advance bug rather than a parsing bug.

## Fix

`grid_expand_track_functions` normalises function-valued track sizes before the
space split:

- `repeat(n, X)` expands to `n` space-separated copies of `X` (n capped at 64);
- `minmax(min, max)` reduces to its `max` — the growth limit, which is what an
  unconstrained track resolves to once free space is distributed. The `min` side
  would need min-content sizing, which this track sizer does not model.

Paren matching is depth-aware so the nested `minmax()` inside `repeat()` is
handled, and `repeat()` is expanded first so its body is reduced afterwards.

Deliberately NOT handled (they still fall through to the pre-existing
reject-and-block-layout path, which is unchanged behaviour, not a new gap):
`auto-fill` / `auto-fit` counts, `fit-content()`, and named grid lines.

## Sabotage triple

Measured 2026-09-12 on `build/cargo-r2/release/simple` (39178424 1789197971).

1. Baseline: `4 examples, 0 failures`.
2. Revert only `val raw = grid_expand_track_functions(raw_declaration)` to
   `val raw = raw_declaration`. Three of four fail, verbatim:
   - `AC-1 ... expected 72 to equal 0` (item 2 is 72 px below item 1, i.e. stacked)
   - `AC-2 ... expected 900 to equal 292` (each item fills the container)
   - `AC-3 ... expected 0 to equal 608` (every item starts at x=0)
3. Restore: `4 examples, 0 failures`.

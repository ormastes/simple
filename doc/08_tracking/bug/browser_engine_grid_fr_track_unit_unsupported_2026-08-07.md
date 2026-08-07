# CSS Grid `fr` track units are unsupported — silently falls back to plain block flow

- **Filed:** 2026-08-07
- **Severity:** P2 — no crash, no wrong-looking output within a naive
  eyeball check, but the CSS Grid `fr`-unit code path never activates.
  `display:grid` with only `fr` tracks silently degrades to plain block
  flow instead of erroring or partially laying out.
- **Affects:** any `grid-template-columns` / `grid-template-rows` declaration
  that uses the `fr` unit, alone or mixed with `px`.
- **Found by:** `test/03_system/gui/web_css/web_css_grid_spec.spl` — example
  `"grid-template-columns: fr tracks are unimplemented (RED-by-design)"`
  (see that spec's file:line), part of unit U3.3 of
  `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`.

## Root cause

`normalized_grid_track_list` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`
(around lines 828-836) walks each whitespace-separated token in a
`grid-template-columns`/`grid-template-rows` value and requires **every**
token to end with the literal `"px"` suffix:

```
# simple_web_html_layout_renderer_declarations.spl:828-836 (paraphrased)
fn normalized_grid_track_list(raw: text) -> text:
    for token in raw.split(" "):
        if not token.ends_with("px"):
            return ""   # whole list rejected, not just the bad token
    raw
```

A track list containing even one `fr` (or any other CSS track-sizing unit:
`%`, `auto`, `minmax()`, `repeat()`) fails this check and the **entire**
list normalizes to the empty string `""`. That empty string then flows into
`st.grid_template_columns`, which is read at
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl:1462-1463`:

```
val grid_columns = grid_track_sizes(st.grid_template_columns)
if st.display == "grid" and grid_columns.len() > 0:
    ... # Grid code path
```

`grid_track_sizes("")` returns an empty list, so `grid_columns.len() > 0`
is false and the Grid code path is skipped entirely — a `display:grid`
container with `fr` tracks lays out as plain block flow. Probed directly:
rendering `#grid{display:grid;grid-template-columns:1fr 2fr;width:60px;...}`
with two children puts both children at `x=0`, full container width, `y=0`
each (stacked block boxes), not split 20px/40px per Grid `fr`-unit
semantics.

## Unblock condition

Implement `fr`-unit parsing in `normalized_grid_track_list` (or a sibling
resolver) that:
1. Recognizes `<n>fr` tokens distinctly from `<n>px` tokens instead of
   rejecting the whole list.
2. Computes remaining free space after fixed (`px`) tracks are subtracted
   from the container's content-box size, then distributes that free space
   across `fr` tracks proportional to their flex factor (CSS Grid §11.5,
   "Resolving Flexible Track Sizes").
3. Feeds the resolved `fr` track pixel sizes into `grid_track_sizes` /
   `grid_track_offset` / `grid_track_span_size` the same way fixed `px`
   tracks already are.

Once landed, flip the RED-by-design example in
`test/03_system/gui/web_css/web_css_grid_spec.spl` (`"grid-template-columns:
fr tracks are unimplemented (RED-by-design)"`) to assert the real
20px/40px split and drop the `(RED-by-design)` qualifier from its name.

## Status

OPEN — unimplemented, not merely surprising per CSS spec. Left RED per
testing-rules RED protocol; do not weaken the assertion.

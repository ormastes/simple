# browser_engine: text does not wrap beside a left float — following block is pushed fully below the float

- **Date:** 2026-08-19
- **Status:** FIXED 2026-08-19 (divergent_s0 14 -> 6; pin lowered, shrink-only)
- **Severity:** medium (layout correctness vs Chrome oracle)
- **Module:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl` (the `layout()` pipeline used by the component-diff harness and BrowserSession rendering)

## Symptom

A left-floated 80x60 box followed by a wrapping paragraph
(`tools/component_diff/fixtures/float_text.html`, 300px container) should
have the paragraph's line boxes flow BESIDE the float and continue below it.
Chrome does; Simple pushes the whole paragraph below the float.

Measured (Chrome for Testing 151.0.7922.34 vs `bin/simple run` extraction,
evidence `tools/component_diff/out/float_text/float_text.state0.diff.txt`):

| node | Chrome | Simple |
|---|---|---|
| `#para` | `[20,20 300x100]` (starts at float's top, 5 lines) | `[20,86 300x60]` (starts BELOW float, 3 lines) |
| `#wrap` | `[10,10 320x156]` | `[10,10 320x182]` |
| `#after` (clear: both) | `[20,126 ...]` | `[20,152 ...]` |

`divergent_s0=14` of 8 node pairs; the float box itself (`#floater`) and the
container x/width agree — the missing piece is specifically inline flow
around the float's band (line boxes with reduced available width).

## Analysis

The renderer places a `float: left` box out of normal flow (siblings' y
advances past it, so it is not treated as a plain block), but the following
block's inline content never gets float-narrowed line boxes: the paragraph
is offset wholesale below the float's bottom edge. A `layout_float.spl`
module exists in the browser_engine directory (M14 layout family) but the
`simple_web_html_layout_renderer` pipeline does not consult float bands when
wrapping inline text. Needs per-line available-width exclusion; not a cheap
inline fix, hence recorded.

## Reproduce

```sh
sh tools/component_diff/run_component_diff.shs --component float_text
cat tools/component_diff/out/float_text/float_text.state0.diff.txt
```

Pinned fail-closed (may shrink, must not grow: `divergent_s0<=14`) in
`test/03_system/browser_engine/chrome_component_set_spec.spl`.

## Fix (2026-08-19)

Mechanism — a left exclusion band in the production layout pipeline
(`simple_web_html_layout_renderer_*`), not the unwired M14 `layout_float.spl`
(that module is StyleProps-based and unreachable from this pipeline; kept as-is):

1. `_style.spl`: new `Style.float_mode: i32 = 0` (0=none, 1=left, 2=right;
   defaulted so the ~250-field constructors stay valid).
2. `_decl_apply.spl`: full-probe `apply_decls` parses `float:` into
   `float_mode_v` and carries it through its Style construction. `"float"` is
   not in `_APPLY_DECLS_DISPATCH_PROPS`, so any rule containing it takes the
   full-probe path. `_declarations.spl` tag-default copies and `_layout.spl`
   `style_with_width/height` copies carry the field.
3. `_layout.spl`: in the block-flow child loop, a `float_mode == 1` child is
   laid out at the current flow position against the left content edge, its
   margin box is recorded as module-level band state
   (`g_float_band_indent` / `g_float_band_bottom`), and `cy` does NOT advance.
   The `#text` branch wraps lines that vertically overlap the band to
   `node_w - indent` via `compute_style_wrap_ranges_float_band` (per-line
   width; font-advance path + cell-width fallback) and resumes full width
   below the band. Bands expire by document y; root `layout()` resets them.

Scope, stated honestly (comments at each site): a single left float per band,
default clear only; `float: right` is parsed but not laid out; multiple
simultaneous floats and explicit `clear` interaction with the band are not
modeled; narrowed lines are not x-shifted at paint time (geometry-oracle fix).

## Evidence

- Before: `divergent_s0=14` (para pushed below float, wrap/after/html/body off).
- After: `divergent_s0=6`; `#para [20,20 300x100]`, `#wrap [10,10 320x156]`,
  `#after [20,126 300x30]`, `html [0,0 800x176]` all match Chrome exactly.
  Residual 6 lines: 2 text-node pairs (font advance/line-height metrics) and
  body (pre-existing margin-collapse divergence, unrelated to floats).
- Pin lowered shrink-only in
  `test/03_system/browser_engine/chrome_component_set_spec.spl` (`[14]` ->
  `[6]`); spec green 6/6.
- Regressions (this worktree, measured with the change vs. stashed baseline —
  identical, i.e. zero introduced): simple_web_css_cascade 8/11 (pre-existing),
  simple_web_layout_child_index 21/22 (pre-existing), chrome_layout_differential
  0/4 (pre-existing), browser_session_dom_input 14/25 with and without the
  change (not worsened).

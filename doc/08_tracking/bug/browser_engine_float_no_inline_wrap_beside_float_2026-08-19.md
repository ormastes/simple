# browser_engine: text does not wrap beside a left float — following block is pushed fully below the float

- **Date:** 2026-08-19
- **Status:** OPEN
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

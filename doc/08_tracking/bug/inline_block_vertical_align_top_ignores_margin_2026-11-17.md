# inline-block with `vertical-align:top` ignores `margin-top`

Found 2026-11-17 while pinning percent margins (`percent_margin_contexts_chrome159_spec`).
Not a percent bug: it happens with a plain px margin.

## Repro

```html
<style>body{margin:0} .c{width:300px;height:100px}
span{display:inline-block;width:20px;height:10px}</style>
<div class=c><span id=s style="margin-top:6px;vertical-align:top"></span></div>
```

| engine | y of `#s` |
|---|---|
| Chrome 159 (`getBoundingClientRect().y`) | 6 |
| Simple (`simple_web_layout_debug_layout_by_id(page, 900, 2000, "s", "y")`) | 0 |

Without `vertical-align:top` (baseline) Simple gives 6, matching Chrome, and `margin-top:2%` in the baseline case gives 6 too.

## Cause (suspected)

In `simple_web_html_layout_renderer_layout_engine.spl` the inline loop only pushes an inline item's vertical margins into `inline_baseline_margin_ts/bs` when it is baseline-aligned (the `cst.vertical_align == "baseline"` condition near line 3606). A top/bottom/middle-aligned item never has its margin added to its y or to the line height.

## Fix sketch

Offset a `top`-aligned item by its resolved `vertical_margin_px_in(cst, true, ...)` and include top+bottom margins in the line box contribution.

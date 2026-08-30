# Simple Web Titlebar Nowrap Specification

> <details>

<!-- sdn-diagram:id=simple_web_titlebar_nowrap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_titlebar_nowrap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_titlebar_nowrap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_titlebar_nowrap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Titlebar Nowrap Specification

## Scenarios

### simple web titlebar nowrap

#### keeps titlebar button labels on one line

- Build a reduced shared-titlebar fixture with a flex title and nowrap button
- Measure the pure-Simple software layout for the titlebar button
- Assert nowrap style is honored and the button stays on one titlebar line
   - Expected: simple_web_layout_debug_style_by_id(html, "run", "white_space_nowrap") equals `true`
   - Expected: simple_web_layout_debug_style_by_id(html, "title", "flex_grow") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a reduced shared-titlebar fixture with a flex title and nowrap button")
val html = "<html><head><style>" +
    "html,body{margin:0;padding:0;background-color:#ffffff}" +
    ".bar{display:flex;align-items:center;width:240px;height:34px;padding:0 14px}" +
    ".title{flex:1;min-width:0;white-space:nowrap}" +
    "#run{min-height:24px;padding:2px 9px;border:1px solid #34d399;box-sizing:border-box;white-space:nowrap;font-size:12px}" +
    "</style></head><body><div class=\"bar\"><span id=\"title\" class=\"title\">Terminal</span><button id=\"run\">Run</button></div></body></html>"

step("Measure the pure-Simple software layout for the titlebar button")
val button_w = simple_web_layout_debug_layout_by_id(html, 320, 80, "run", "w").to_i32()
val button_h = simple_web_layout_debug_layout_by_id(html, 320, 80, "run", "h").to_i32()

step("Assert nowrap style is honored and the button stays on one titlebar line")
expect(simple_web_layout_debug_style_by_id(html, "run", "white_space_nowrap")).to_equal("true")
expect(simple_web_layout_debug_style_by_id(html, "title", "flex_grow")).to_equal("1")
expect(button_w).to_be_greater_than(32)
expect(button_h).to_be_less_than(30)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/simple_web_titlebar_nowrap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple web titlebar nowrap

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

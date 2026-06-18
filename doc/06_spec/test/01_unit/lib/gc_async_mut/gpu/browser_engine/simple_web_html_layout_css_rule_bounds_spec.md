# Simple Web HTML Layout CSS Rule Bounds Spec

> The HTML layout renderer allocates cascade arrays from the CSS rule count pass. Pathological style blocks must not create unbounded rule arrays or keep scanning after the cap has been filled.

<!-- sdn-diagram:id=simple_web_html_layout_css_rule_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_html_layout_css_rule_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_html_layout_css_rule_bounds_spec -> std
simple_web_html_layout_css_rule_bounds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_html_layout_css_rule_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web HTML Layout CSS Rule Bounds Spec

The HTML layout renderer allocates cascade arrays from the CSS rule count pass. Pathological style blocks must not create unbounded rule arrays or keep scanning after the cap has been filled.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_css_rule_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The HTML layout renderer allocates cascade arrays from the CSS rule count pass.
Pathological style blocks must not create unbounded rule arrays or keep scanning
after the cap has been filled.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and debug style assertions.

## Scenarios

### SimpleWebHtmlLayoutCssRuleBounds

#### caps style block rules while preserving admitted early rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filler = str_repeat(".dummy { height: 1px; }\n", simple_web_layout_debug_max_css_rule_count())
val html = "<style>.early { width: 12px; }\n" + filler + ".over { width: 34px; }</style><main><div id='early' class='early'></div><div id='over' class='over'></div></main>"

expect(simple_web_layout_debug_style_by_id(html, "early", "width")).to_equal("12")
expect(simple_web_layout_debug_style_by_id(html, "over", "width")).to_equal("0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>

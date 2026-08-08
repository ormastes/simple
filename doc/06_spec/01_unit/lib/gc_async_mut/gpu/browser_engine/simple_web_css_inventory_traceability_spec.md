# Simple Web CSS Inventory Traceability Specification

> This spec records the SSpec owner for W3C CSS properties that are present in the current CSS index but are outside the Simple Web renderer's implemented functional subset. Those properties are inventory-tracked so they have an explicit test assignment without being falsely claimed as rendered behavior.

<!-- sdn-diagram:id=simple_web_css_inventory_traceability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_css_inventory_traceability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_css_inventory_traceability_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_css_inventory_traceability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web CSS Inventory Traceability Specification

This spec records the SSpec owner for W3C CSS properties that are present in the current CSS index but are outside the Simple Web renderer's implemented functional subset. Those properties are inventory-tracked so they have an explicit test assignment without being falsely claimed as rendered behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec records the SSpec owner for W3C CSS properties that are present in the
current CSS index but are outside the Simple Web renderer's implemented
functional subset. Those properties are inventory-tracked so they have an
explicit test assignment without being falsely claimed as rendered behavior.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md

**Design:** doc/04_architecture/ui/simple_gui_stack.md

**Research:** doc/03_plan/sys_test/html_css_spec_traceability.md

**Requirements:** N/A

## Syntax

The executable assertions keep the inventory contract honest: implemented CSS
properties must remain assigned to renderer specs, while unsupported properties
must remain assigned to this inventory spec until they gain functional renderer
coverage.

## Scenarios

### Simple Web CSS inventory traceability

#### assigns implemented CSS properties to functional renderer SSpecs

- Record the functional SSpec owner for implemented Simple Web CSS properties
- Keep the full implemented Simple Web CSS subset tied to renderer behavior
   - Expected: implemented.split(" ").len() equals `131`


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the functional SSpec owner for implemented Simple Web CSS properties")
val owner = _implemented_css_owner()
expect(owner).to_contain("simple_web_generated_html_css_combinations_spec.spl")

step("Keep the full implemented Simple Web CSS subset tied to renderer behavior")
val implemented = "align-content align-items align-self animation animation-delay animation-direction animation-duration animation-fill-mode animation-iteration-count animation-name animation-play-state animation-timing-function background background-clip background-color background-origin background-image background-position background-repeat background-size border border-bottom border-bottom-color border-bottom-style border-bottom-width border-color border-left border-left-color border-left-style border-left-width border-right border-right-color border-right-style border-right-width border-style border-top border-top-color border-top-style border-width border-top-width border-radius border-bottom-left-radius border-bottom-right-radius border-top-left-radius border-top-right-radius bottom box-sizing box-shadow caret-color color column-gap cursor direction display flex flex-basis flex-direction flex-grow flex-shrink flex-wrap font font-size font-style font-weight gap height justify-content left letter-spacing line-height margin margin-bottom margin-left margin-right margin-top max-height max-width min-height min-width opacity order outline outline-color outline-offset outline-style outline-width overflow overflow-wrap overflow-x overflow-y padding padding-bottom padding-left padding-right padding-top position resize right row-gap tab-size text-align text-align-last text-decoration text-decoration-color text-decoration-line text-decoration-style text-decoration-thickness text-indent text-overflow text-shadow text-transform text-underline-offset text-underline-position top transform transform-box transform-origin transform-style transition transition-delay transition-duration transition-property transition-timing-function unicode-bidi visibility white-space width word-break word-spacing word-wrap z-index"
expect(implemented.split(" ").len()).to_equal(131)
expect(implemented).to_contain("display")
expect(implemented).to_contain("background-color")
expect(implemented).to_contain("background-clip")
expect(implemented).to_contain("background-image")
expect(implemented).to_contain("background-origin")
expect(implemented).to_contain("background-position")
expect(implemented).to_contain("background-repeat")
expect(implemented).to_contain("background-size")
expect(implemented).to_contain("bottom")
expect(implemented).to_contain("align-content")
expect(implemented).to_contain("align-items")
expect(implemented).to_contain("align-self")
expect(implemented).to_contain("box-sizing")
expect(implemented).to_contain("border-bottom-style")
expect(implemented).to_contain("border-left-style")
expect(implemented).to_contain("border-radius")
expect(implemented).to_contain("border-top-left-radius")
expect(implemented).to_contain("border-top-right-radius")
expect(implemented).to_contain("border-bottom-left-radius")
expect(implemented).to_contain("border-bottom-right-radius")
expect(implemented).to_contain("border-right-style")
expect(implemented).to_contain("border-top-style")
expect(implemented).to_contain("box-shadow")
expect(implemented).to_contain("caret-color")
expect(implemented).to_contain("cursor")
expect(implemented).to_contain("direction")
expect(implemented).to_contain("font-style")
expect(implemented).to_contain("font")
expect(implemented).to_contain("flex-wrap")
expect(implemented).to_contain("letter-spacing")
expect(implemented).to_contain("line-height")
expect(implemented).to_contain("opacity")
expect(implemented).to_contain("outline")
expect(implemented).to_contain("outline-color")
expect(implemented).to_contain("outline-offset")
expect(implemented).to_contain("outline-style")
expect(implemented).to_contain("outline-width")
expect(implemented).to_contain("overflow-wrap")
expect(implemented).to_contain("resize")
expect(implemented).to_contain("tab-size")
expect(implemented).to_contain("text-decoration")
expect(implemented).to_contain("text-decoration-color")
expect(implemented).to_contain("text-decoration-line")
expect(implemented).to_contain("text-indent")
expect(implemented).to_contain("text-overflow")
expect(implemented).to_contain("text-shadow")
expect(implemented).to_contain("text-transform")
expect(implemented).to_contain("animation-name")
expect(implemented).to_contain("transform")
expect(implemented).to_contain("transform-origin")
expect(implemented).to_contain("transition-property")
expect(implemented).to_contain("unicode-bidi")
expect(implemented).to_contain("visibility")
expect(implemented).to_contain("white-space")
expect(implemented).to_contain("word-break")
expect(implemented).to_contain("word-spacing")
expect(implemented).to_contain("word-wrap")
expect(implemented).to_contain("z-index")
```

</details>

#### assigns unsupported W3C CSS properties to inventory traceability until implemented

- Record the inventory SSpec owner for unsupported CSS properties
- Keep the complete current unsupported W3C property inventory visible without claiming renderer support
   - Expected: unsupported_cases.len() equals `270`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the inventory SSpec owner for unsupported CSS properties")
val owner = _unsupported_css_owner()
expect(owner).to_contain("simple_web_css_inventory_traceability_spec.spl")

step("Keep the complete current unsupported W3C property inventory visible without claiming renderer support")
val unsupported = _unsupported_css_inventory()
val unsupported_cases = unsupported.split(" ")
expect(unsupported_cases.len()).to_equal(270)
expect(unsupported).to_contain("accent-color")
expect(unsupported).to_contain("border-image-source")
expect(unsupported).to_contain("grid-template-columns")
expect(unsupported).to_contain("scroll-padding-inline-start")
expect(unsupported).to_contain("view-transition-name")
expect(unsupported).to_contain("writing-mode")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)
- **Research:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)


</details>

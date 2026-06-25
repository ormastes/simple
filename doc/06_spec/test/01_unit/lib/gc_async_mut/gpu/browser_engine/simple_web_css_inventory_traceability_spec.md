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
   - Expected: implemented.split(" ").len() equals `85`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the functional SSpec owner for implemented Simple Web CSS properties")
val owner = _implemented_css_owner()
expect(owner).to_contain("simple_web_generated_html_css_combinations_spec.spl")

step("Keep the full implemented Simple Web CSS subset tied to renderer behavior")
val implemented = "align-content align-items align-self background background-color border border-bottom border-bottom-color border-bottom-style border-bottom-width border-color border-left border-left-color border-left-style border-left-width border-right border-right-color border-right-style border-right-width border-style border-top border-top-color border-top-style border-top-width border-width bottom box-sizing color column-gap direction display flex flex-basis flex-direction flex-grow flex-shrink flex-wrap font-size font-style font-weight gap height justify-content left letter-spacing line-height margin margin-bottom margin-left margin-right margin-top max-height max-width min-height min-width opacity order outline outline-color outline-style outline-width overflow overflow-x overflow-y padding padding-bottom padding-left padding-right padding-top position right row-gap text-align text-decoration text-decoration-line text-indent text-shadow text-transform top transform visibility white-space width word-spacing z-index"
expect(implemented.split(" ").len()).to_equal(85)
expect(implemented).to_contain("display")
expect(implemented).to_contain("background-color")
expect(implemented).to_contain("bottom")
expect(implemented).to_contain("align-content")
expect(implemented).to_contain("align-items")
expect(implemented).to_contain("align-self")
expect(implemented).to_contain("box-sizing")
expect(implemented).to_contain("border-bottom-style")
expect(implemented).to_contain("border-left-style")
expect(implemented).to_contain("border-right-style")
expect(implemented).to_contain("border-top-style")
expect(implemented).to_contain("direction")
expect(implemented).to_contain("font-style")
expect(implemented).to_contain("flex-wrap")
expect(implemented).to_contain("letter-spacing")
expect(implemented).to_contain("line-height")
expect(implemented).to_contain("opacity")
expect(implemented).to_contain("outline")
expect(implemented).to_contain("outline-color")
expect(implemented).to_contain("outline-style")
expect(implemented).to_contain("outline-width")
expect(implemented).to_contain("text-decoration")
expect(implemented).to_contain("text-decoration-line")
expect(implemented).to_contain("text-indent")
expect(implemented).to_contain("text-shadow")
expect(implemented).to_contain("text-transform")
expect(implemented).to_contain("transform")
expect(implemented).to_contain("visibility")
expect(implemented).to_contain("white-space")
expect(implemented).to_contain("word-spacing")
expect(implemented).to_contain("z-index")
```

</details>

#### assigns unsupported W3C CSS properties to inventory traceability until implemented

- Record the inventory SSpec owner for unsupported CSS properties
- Keep the complete current unsupported W3C property inventory visible without claiming renderer support
   - Expected: unsupported_cases.len() equals `316`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the inventory SSpec owner for unsupported CSS properties")
val owner = _unsupported_css_owner()
expect(owner).to_contain("simple_web_css_inventory_traceability_spec.spl")

step("Keep the complete current unsupported W3C property inventory visible without claiming renderer support")
val unsupported = _unsupported_css_inventory()
val unsupported_cases = unsupported.split(" ")
expect(unsupported_cases.len()).to_equal(316)
expect(unsupported).to_contain("accent-color")
expect(unsupported).to_contain("animation-direction")
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

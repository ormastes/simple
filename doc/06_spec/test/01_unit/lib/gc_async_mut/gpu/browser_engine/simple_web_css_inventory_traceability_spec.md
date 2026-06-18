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
- Keep representative implemented properties tied to renderer behavior


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the functional SSpec owner for implemented Simple Web CSS properties")
val owner = _implemented_css_owner()
expect(owner).to_contain("simple_web_generated_html_css_combinations_spec.spl")

step("Keep representative implemented properties tied to renderer behavior")
val implemented = "display flex flex-basis flex-direction flex-grow flex-shrink gap padding padding-bottom padding-right padding-top border background-color border-bottom-color border-bottom-width border-left-color border-left-width border-right-color border-right-width border-top-color border-top-width color font-size width height margin margin-bottom margin-right overflow position z-index"
expect(implemented).to_contain("display")
expect(implemented).to_contain("background-color")
expect(implemented).to_contain("z-index")
```

</details>

#### assigns unsupported W3C CSS properties to inventory traceability until implemented

- Record the inventory SSpec owner for unsupported CSS properties
- Keep representative unsupported properties visible without claiming renderer support


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the inventory SSpec owner for unsupported CSS properties")
val owner = _unsupported_css_owner()
expect(owner).to_contain("simple_web_css_inventory_traceability_spec.spl")

step("Keep representative unsupported properties visible without claiming renderer support")
val unsupported = "accent-color animation-delay aspect-ratio background-image border-radius grid-template-columns mask-image scroll-padding transform transition writing-mode"
expect(unsupported).to_contain("accent-color")
expect(unsupported).to_contain("grid-template-columns")
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

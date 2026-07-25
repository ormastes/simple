# Style Specification

> <details>

<!-- sdn-diagram:id=style_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=style_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

style_spec -> std
style_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=style_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Specification

## Scenarios

### resolve_style

#### cascades lower specificity before higher specificity

- var sheet = StyleSheet new
- sheet add rule
- sheet add rule
   - Expected: resolved.color.color equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = StyleSheet.new()
sheet.add_rule(StyleSelector.by_id("save"), _color_rule("red"))
sheet.add_rule(StyleSelector.by_kind("button"), _color_rule("blue"))

val resolved = resolve_style(sheet, "save", "button", "", "")

expect(resolved.color.color).to_equal("red")
```

</details>

#### preserves sheet order for equal specificity rules

- var sheet = StyleSheet new
- sheet add rule
- sheet add rule
   - Expected: resolved.color.color equals `green`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = StyleSheet.new()
sheet.add_rule(StyleSelector.by_kind("button"), _color_rule("blue"))
sheet.add_rule(StyleSelector.by_kind("button"), _color_rule("green"))

val resolved = resolve_style(sheet, "save", "button", "", "")

expect(resolved.color.color).to_equal("green")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/style_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- resolve_style

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

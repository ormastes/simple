# Layout Text Node Specification

> <details>

<!-- sdn-diagram:id=layout_text_node_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_text_node_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_text_node_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_text_node_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Text Node Specification

## Scenarios

### Block text node wrapping

#### keeps normal unbroken text on one overflowing line

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.text("supercalifragilistic")
val style = be_default_style()
val box_ = layout_text_node(node, _container(40), style, FloatContext.create())
expect(box_.height).to_equal(19)
expect(box_.width).to_be_greater_than(40)
```

</details>

#### wraps unbroken text when overflow-wrap break-word is set

1. var style = be default style
   - Expected: box_.width equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.text("supercalifragilistic")
var style = be_default_style()
style.overflow_wrap = "break-word"
val box_ = layout_text_node(node, _container(40), style, FloatContext.create())
expect(box_.height).to_be_greater_than(19)
expect(box_.width).to_equal(40)
```

</details>

#### keeps whitespace text eligible for normal wrapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.text("word word word word word")
val style = be_default_style()
val box_ = layout_text_node(node, _container(40), style, FloatContext.create())
expect(box_.height).to_be_greater_than(19)
```

</details>

#### detects whitespace break opportunities

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(layout_text_has_break_opportunity("abc def")).to_equal(true)
expect(layout_text_has_break_opportunity("abcdef")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/layout_text_node_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Block text node wrapping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

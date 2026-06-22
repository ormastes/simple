# Responsive Widget Specification

> <details>

<!-- sdn-diagram:id=responsive_widget_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=responsive_widget_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

responsive_widget_spec -> std
responsive_widget_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=responsive_widget_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Responsive Widget Specification

## Scenarios

### SizeClass.to_wire

#### compact serializes to lowercase compact

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SizeClass.Compact.to_wire()).to_equal("compact")
```

</details>

#### regular serializes to lowercase regular

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SizeClass.Regular.to_wire()).to_equal("regular")
```

</details>

#### expanded serializes to lowercase expanded

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SizeClass.Expanded.to_wire()).to_equal("expanded")
```

</details>

### Orientation.to_wire

#### landscape serializes to lowercase landscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Orientation.Landscape.to_wire()).to_equal("landscape")
```

</details>

#### portrait serializes to lowercase portrait

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Orientation.Portrait.to_wire()).to_equal("portrait")
```

</details>

#### square serializes to lowercase square

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Orientation.Square.to_wire()).to_equal("square")
```

</details>

### with_responsive_layout

#### stores compact layout prop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("w1", "hello")
val n = with_responsive_layout(node, "vbox", "hbox", "grid")
expect(n.get_prop("responsive_compact")).to_equal("vbox")
```

</details>

#### stores regular layout prop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("w2", "hello")
val n = with_responsive_layout(node, "vbox", "hbox", "grid")
expect(n.get_prop("responsive_regular")).to_equal("hbox")
```

</details>

#### stores expanded layout prop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("w3", "hello")
val n = with_responsive_layout(node, "vbox", "hbox", "grid")
expect(n.get_prop("responsive_expanded")).to_equal("grid")
```

</details>

### with_responsive_columns

#### stores compact column count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("g1", "x")
val n = with_responsive_columns(node, 1, 2, 4)
expect(n.get_prop("responsive_cols_compact")).to_equal("1")
```

</details>

#### stores regular column count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("g2", "x")
val n = with_responsive_columns(node, 1, 2, 4)
expect(n.get_prop("responsive_cols_regular")).to_equal("2")
```

</details>

#### stores expanded column count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("g3", "x")
val n = with_responsive_columns(node, 1, 2, 4)
expect(n.get_prop("responsive_cols_expanded")).to_equal("4")
```

</details>

### with_show_when_at_most

#### stores compact threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("sm1", "x")
val n = with_show_when_at_most(node, SizeClass.Compact)
expect(n.get_prop("show_when_at_most")).to_equal("compact")
```

</details>

#### stores regular threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("sm2", "x")
val n = with_show_when_at_most(node, SizeClass.Regular)
expect(n.get_prop("show_when_at_most")).to_equal("regular")
```

</details>

### with_show_when_at_least

#### stores expanded threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("sl1", "x")
val n = with_show_when_at_least(node, SizeClass.Expanded)
expect(n.get_prop("show_when_at_least")).to_equal("expanded")
```

</details>

### with_show_when_orientation

#### stores portrait orientation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("so1", "x")
val n = with_show_when_orientation(node, Orientation.Portrait)
expect(n.get_prop("show_when_orientation")).to_equal("portrait")
```

</details>

#### stores landscape orientation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("so2", "x")
val n = with_show_when_orientation(node, Orientation.Landscape)
expect(n.get_prop("show_when_orientation")).to_equal("landscape")
```

</details>

### WidgetNode.responsive_columns

#### stores all three column counts via method

1. var node = text widget
2. node = node responsive columns
   - Expected: node.get_prop("responsive_cols_compact") equals `1`
   - Expected: node.get_prop("responsive_cols_regular") equals `2`
   - Expected: node.get_prop("responsive_cols_expanded") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("mn1", "x")
node = node.responsive_columns(1, 2, 4)
expect(node.get_prop("responsive_cols_compact")).to_equal("1")
expect(node.get_prop("responsive_cols_regular")).to_equal("2")
expect(node.get_prop("responsive_cols_expanded")).to_equal("4")
```

</details>

### WidgetNode.responsive_layout

#### stores all three layout names via method

1. var node = text widget
2. node = node responsive layout
   - Expected: node.get_prop("responsive_compact") equals `vbox`
   - Expected: node.get_prop("responsive_regular") equals `hbox`
   - Expected: node.get_prop("responsive_expanded") equals `grid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("mn2", "x")
node = node.responsive_layout("vbox", "hbox", "grid")
expect(node.get_prop("responsive_compact")).to_equal("vbox")
expect(node.get_prop("responsive_regular")).to_equal("hbox")
expect(node.get_prop("responsive_expanded")).to_equal("grid")
```

</details>

### WidgetNode.show_when_at_most

#### stores threshold via method

1. var node = text widget
2. node = node show when at most
   - Expected: node.get_prop("show_when_at_most") equals `compact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("mn3", "x")
node = node.show_when_at_most(SizeClass.Compact)
expect(node.get_prop("show_when_at_most")).to_equal("compact")
```

</details>

### WidgetNode.show_when_at_least

#### stores threshold via method

1. var node = text widget
2. node = node show when at least
   - Expected: node.get_prop("show_when_at_least") equals `regular`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("mn4", "x")
node = node.show_when_at_least(SizeClass.Regular)
expect(node.get_prop("show_when_at_least")).to_equal("regular")
```

</details>

### WidgetNode.show_when_orientation

#### stores orientation via method

1. var node = text widget
2. node = node show when orientation
   - Expected: node.get_prop("show_when_orientation") equals `portrait`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("mn5", "x")
node = node.show_when_orientation(Orientation.Portrait)
expect(node.get_prop("show_when_orientation")).to_equal("portrait")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/responsive_widget_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SizeClass.to_wire
- Orientation.to_wire
- with_responsive_layout
- with_responsive_columns
- with_show_when_at_most
- with_show_when_at_least
- with_show_when_orientation
- WidgetNode.responsive_columns
- WidgetNode.responsive_layout
- WidgetNode.show_when_at_most
- WidgetNode.show_when_at_least
- WidgetNode.show_when_orientation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Element Specification

> 1. expect true  # NodeId new

<!-- sdn-diagram:id=element_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=element_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

element_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=element_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Element Specification

## Scenarios

### NodeId

#### creates unique IDs

1. expect true  # NodeId new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # NodeId.new(1).value() == 1
```

</details>

#### generates sequential IDs

1. expect true  # id next


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # id.next().value() == id.value() + 1
```

</details>

#### compares for equality

1. expect true  # NodeId new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # NodeId.new(42) == NodeId.new(42)
```

</details>

### ElementKind

#### identifies block elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Div, Box, Paragraph, Column are block
```

</details>

#### identifies inline elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Span, Text, Button are inline
```

</details>

#### identifies interactive elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Button, Input, Checkbox are interactive
```

</details>

#### provides HTML tag names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Div->"div", Button->"button", etc.
```

</details>

### Element

#### creates elements with given kind

1. expect true  # Element new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Element.new(id, ElementKind.Div)
```

</details>

#### creates text elements

1. expect true  # Element text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Element.text(id, "Hello, World!")
```

</details>

#### creates button elements with tab index

1. expect true  # Element button


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Element.button(id, "Click Me")
```

</details>

#### supports builder pattern

1. expect true  #  with key


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # .with_key().with_attr().with_class().with_style()
```

</details>

#### adds children

1. expect true  #  with child


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # .with_child(Element.text(id, "Child"))
```

</details>

#### finds child by index

1. expect true  # parent child at


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # parent.child_at(0)
```

</details>

#### finds child by key

1. expect true  # parent find by key


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # parent.find_by_key("special")
```

</details>

#### finds descendant by ID

1. expect true  # root find by id


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # root.find_by_id(grandchild_id)
```

</details>

#### manages focus state

1. expect true  # elem focus


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # elem.focus(), elem.blur(), elem.focused
```

</details>

### ElementTree

#### creates tree with root element

1. expect true  # ElementTree new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # ElementTree.new(ElementKind.Div)
```

</details>

#### allocates sequential node IDs

1. expect true  # tree alloc id


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # tree.alloc_id()
```

</details>

#### manages focus

1. expect true  # tree set focus


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # tree.set_focus(id), tree.focused()
```

</details>

#### cycles focus through focusable elements

1. expect true  # tree focus next


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # tree.focus_next(), tree.focus_prev()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/element_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NodeId
- ElementKind
- Element
- ElementTree

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

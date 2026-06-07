# Html Render Specification

> <details>

<!-- sdn-diagram:id=html_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_render_spec -> common
html_render_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Render Specification

## Scenarios

### render_html_widget text

#### renders div with class widget-text

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("txt1", "Hello World")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-text"
```

</details>

#### renders content inside the div

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("txt2", "Some content")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Some content"
```

</details>

#### renders as a div tag

1. expect html starts with


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("txt3", "Test")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<div") to_equal true
```

</details>

### render_html_widget button

#### renders button tag with class widget-button

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = button("btn1", "Click Me", "do_click")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-button"
```

</details>

#### renders as a button tag

1. expect html starts with


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = button("btn2", "OK", "confirm")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<button") to_equal true
```

</details>

#### includes data-action attribute

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = button("btn3", "Save", "save_file")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-action=\"save_file\""
```

</details>

#### includes label text as content

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = button("btn4", "Submit", "submit")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Submit"
```

</details>

### render_html_widget panel

#### renders div with class widget-panel

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = panel("pnl1", "My Panel", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-panel"
```

</details>

#### renders children inside panel

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = text_widget("pnl_child", "Inner text")
val node = panel("pnl2", "Parent", [child])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Inner text"
expect html to_contain "widget-text"
```

</details>

### render_html_widget progress

#### renders div with class widget-progress

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog1", 75)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-progress"
```

</details>

#### includes percentage in style

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog2", 42)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "width: 42%"
```

</details>

#### includes percentage text

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog3", 90)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "90%"
```

</details>

### render_html_widget checkbox

#### renders label with class widget-checkbox

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = checkbox("chk1", "Accept terms", false)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-checkbox"
```

</details>

#### renders input with type checkbox

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = checkbox("chk2", "Enable feature", false)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "type=\"checkbox\""
```

</details>

#### renders as a div tag

1. expect html starts with


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = checkbox("chk3", "Option", false)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<div") to_equal true
```

</details>

#### includes checked attribute when checked is true

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = checkbox("chk4", "Agree", true)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain " checked"
```

</details>

#### omits checked attribute when checked is false

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = checkbox("chk5", "Disagree", false)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
# The unchecked checkbox should not have the checked attribute
# The output contains type="checkbox" but NOT an extra " checked" attr
val has_checked_attr = html.contains("checked /")
expect has_checked_attr to_equal false
```

</details>

### render_html_widget image

#### renders img tag with class widget-image

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img1", "logo.png", "Logo")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-image"
```

</details>

#### renders as an img tag

1. expect html starts with


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img2", "photo.jpg", "Photo")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<img") to_equal true
```

</details>

#### includes src attribute

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img3", "banner.png", "Banner")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "src=\"banner.png\""
```

</details>

#### includes alt attribute

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img4", "icon.svg", "App Icon")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "alt=\"App Icon\""
```

</details>

### render_html_widget divider

#### renders hr tag with class widget-divider

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = divider("div1")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-divider"
```

</details>

#### renders as an hr tag

1. expect html starts with


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = divider("div2")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<hr") to_equal true
```

</details>

### render_html_widget focus

#### adds focused class when widget is focused

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("foc1", "Focused text")
val tree = UITree.new(node)
# init_state sets focused_id to the first widget id (the root)
val state = init_state(tree)
# foc1 is the root so it gets focus
expect state.focused_id to_equal "foc1"
val html = render_html_widget(node, state)
expect html to_contain " focused"
```

</details>

#### does not add focused class when widget is not focused

1. var parent = panel


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create a tree where the focused widget is NOT the one we render
val root = text_widget("foc_root", "Root")
val other = text_widget("foc_other", "Other")
var parent = panel("foc_parent", "Panel", [root, other])
val tree = UITree.new(parent)
val state = init_state(tree)
# state.focused_id will be "foc_parent" (the tree root)
# Render a non-focused child
val html = render_html_widget(other, state)
val class_segment = "widget-text\""
# The class should be widget-text" without focused
expect html to_contain class_segment
```

</details>

### render_html_tree

#### recursively renders full tree with nested elements

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child1 = text_widget("tree_txt", "Hello from tree")
val child2 = button("tree_btn", "Go", "go_action")
val root = panel("tree_root", "Tree Panel", [child1, child2])
val tree = UITree.new(root)
val state = init_state(tree)
val html = render_html_tree(root, state)
expect html to_contain "widget-panel"
expect html to_contain "widget-text"
expect html to_contain "Hello from tree"
expect html to_contain "widget-button"
expect html to_contain "Go"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/html_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- render_html_widget text
- render_html_widget button
- render_html_widget panel
- render_html_widget progress
- render_html_widget checkbox
- render_html_widget image
- render_html_widget divider
- render_html_widget focus
- render_html_tree

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

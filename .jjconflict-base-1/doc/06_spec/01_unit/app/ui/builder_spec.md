# Builder Specification

> <details>

<!-- sdn-diagram:id=builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

builder_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Builder Specification

## Scenarios

### Container builders

#### column

#### creates panel with vbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = WidgetNode.new("col_child1", "text")
val c2 = WidgetNode.new("col_child2", "text")
val col = column("col1", [c1, c2])
expect col.kind to_equal "panel"
expect col.layout to_equal "vbox"
```

</details>

#### has correct child count

1. expect col child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = WidgetNode.new("col2_a", "text")
val c2 = WidgetNode.new("col2_b", "text")
val col = column("col2", [c1, c2])
expect col.child_count() to_equal 2
```

</details>

#### creates empty column with no children

1. expect col child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column("col_empty", [])
expect col.kind to_equal "panel"
expect col.child_count() to_equal 0
```

</details>

#### row

#### creates panel with hbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = WidgetNode.new("row_child1", "text")
val r = row("row1", [c1])
expect r.kind to_equal "panel"
expect r.layout to_equal "hbox"
```

</details>

#### has correct child count

1. expect r child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = WidgetNode.new("row2_a", "text")
val c2 = WidgetNode.new("row2_b", "text")
val c3 = WidgetNode.new("row2_c", "text")
val r = row("row2", [c1, c2, c3])
expect r.child_count() to_equal 3
```

</details>

#### grid

#### creates panel with grid layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = WidgetNode.new("grid_child1", "text")
val g = builder.grid("grid1", [c1])
expect g.kind to_equal "panel"
expect g.layout to_equal "grid"
```

</details>

#### has correct child count

1. expect g child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = WidgetNode.new("grid2_a", "text")
val c2 = WidgetNode.new("grid2_b", "text")
val g = builder.grid("grid2", [c1, c2])
expect g.child_count() to_equal 2
```

</details>

#### panel

#### creates panel with title prop

1. expect p get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = WidgetNode.new("pan_child", "text")
val p = panel("pan1", "My Panel", [child])
expect p.kind to_equal "panel"
expect p.get_prop("title") to_equal "My Panel"
```

</details>

#### uses vbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("pan2", "Title", [])
expect p.layout to_equal "vbox"
```

</details>

#### has children

1. expect p child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = WidgetNode.new("pan3_a", "text")
val c2 = WidgetNode.new("pan3_b", "button")
val p = panel("pan3", "Container", [c1, c2])
expect p.child_count() to_equal 2
```

</details>

### Leaf widget builders

#### text_widget

#### creates text with content prop

1. expect tw get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tw = text_widget("tw1", "Hello World")
expect tw.kind to_equal "text"
expect tw.get_prop("content") to_equal "Hello World"
```

</details>

#### handles empty content

1. expect tw get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tw = text_widget("tw2", "")
expect tw.get_prop("content") to_equal ""
```

</details>

#### label

#### creates text with label prop

1. expect lbl get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbl = label("lbl1", "Username:")
expect lbl.kind to_equal "text"
expect lbl.get_prop("label") to_equal "Username:"
```

</details>

#### input

#### creates input with placeholder prop

1. expect inp get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inp = text_input("inp1", "Enter text...")
expect inp.kind to_equal "input"
expect inp.get_prop("placeholder") to_equal "Enter text..."
```

</details>

#### button

#### creates button with label and action props

1. expect btn get prop
2. expect btn get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn1", "Click Me", "submit")
expect btn.kind to_equal "button"
expect btn.get_prop("label") to_equal "Click Me"
expect btn.get_prop("action") to_equal "submit"
```

</details>

#### checkbox

#### creates checked checkbox

1. expect cb get prop
2. expect cb get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb1", "Accept Terms", true)
expect cb.kind to_equal "checkbox"
expect cb.get_prop("label") to_equal "Accept Terms"
expect cb.get_prop("checked") to_equal "true"
```

</details>

#### creates unchecked checkbox

1. expect cb get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb2", "Subscribe", false)
expect cb.get_prop("checked") to_equal "false"
```

</details>

#### text_field

#### creates textfield with value and placeholder

1. expect tf get prop
2. expect tf get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tf = text_field("tf1", "initial", "Type here")
expect tf.kind to_equal "textfield"
expect tf.get_prop("value") to_equal "initial"
expect tf.get_prop("placeholder") to_equal "Type here"
```

</details>

#### image

#### creates image with src and alt

1. expect img get prop
2. expect img get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img1", "https://example.com/pic.png", "A photo")
expect img.kind to_equal "image"
expect img.get_prop("src") to_equal "https://example.com/pic.png"
expect img.get_prop("alt") to_equal "A photo"
```

</details>

#### divider

#### creates divider widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val div = divider("div1")
expect div.kind to_equal "divider"
```

</details>

#### progress

#### creates progress bar with value

1. expect pb get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pb = progress("pb1", 75)
expect pb.kind to_equal "progress"
expect pb.get_prop("value") to_equal "75"
```

</details>

#### creates progress bar with zero

1. expect pb get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pb = progress("pb2", 0)
expect pb.get_prop("value") to_equal "0"
```

</details>

### Composite widget builders

#### dropdown

#### creates dropdown with option children

1. expect dd child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd1", ["Apple", "Banana"])
expect dd.kind to_equal "dropdown"
expect dd.child_count() to_equal 2
```

</details>

#### option children have label props

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd2", ["Red", "Green", "Blue"])
val first = dd.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "Red"
```

</details>

#### creates empty dropdown with no items

1. expect dd child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd3", [])
expect dd.child_count() to_equal 0
```

</details>

#### menubar

#### creates menubar with text children

1. expect mb child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mb = menubar("mb1", ["File", "Edit"])
expect mb.kind to_equal "menubar"
expect mb.child_count() to_equal 2
```

</details>

#### menu children have label props

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mb = menubar("mb2", ["View", "Help"])
val first = mb.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "View"
```

</details>

#### statusbar

#### creates statusbar with left and right props

1. expect sb get prop
2. expect sb get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = statusbar("sb1", "Ready", "Ln 42")
expect sb.kind to_equal "statusbar"
expect sb.get_prop("left") to_equal "Ready"
expect sb.get_prop("right") to_equal "Ln 42"
```

</details>

#### tabs

#### creates tabs with labeled children

1. expect tb child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tb = tabs("tb1", ["Tab1", "Tab2"])
expect tb.kind to_equal "tabs"
expect tb.child_count() to_equal 2
```

</details>

#### tab children have label props

1. expect second get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tb = tabs("tb2", ["Home", "Settings", "About"])
val second = tb.child_at(1)
expect second != nil to_equal true
expect second.get_prop("label") to_equal "Settings"
```

</details>

#### list_widget

#### creates list with item children

1. expect lw child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("lw1", ["Alpha", "Beta", "Gamma"])
expect lw.kind to_equal "list"
expect lw.child_count() to_equal 3
```

</details>

#### item children have label props

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("lw2", ["First", "Second"])
val first = lw.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "First"
```

</details>

#### dialog

#### creates dialog with title prop

1. expect dlg get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dlg = dialog("dlg1", "Confirm", [])
expect dlg.kind to_equal "dialog"
expect dlg.get_prop("title") to_equal "Confirm"
```

</details>

#### dialog has vbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dlg = dialog("dlg2", "Alert", [])
expect dlg.layout to_equal "vbox"
```

</details>

#### tooltip

#### creates tooltip with content and target

1. expect tt get prop
2. expect tt get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt1", "Help text", "btn_target")
expect tt.kind to_equal "tooltip"
expect tt.get_prop("content") to_equal "Help text"
expect tt.get_prop("target") to_equal "btn_target"
```

</details>

### Tree builders

#### build_tree

#### wraps root in UITree

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("bt_root", "panel")
val tree = build_tree(root)
expect tree.root.id to_equal "bt_root"
```

</details>

#### uses default title

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("bt_root2", "panel")
val tree = build_tree(root)
expect tree.title to_equal "Simple UI"
```

</details>

#### uses default theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("bt_root3", "panel")
val tree = build_tree(root)
expect tree.theme to_equal "dark"
```

</details>

#### build_tree_with_title

#### sets custom title

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("btt_root1", "panel")
val tree = build_tree_with_title(root, "My App", "dark")
expect tree.title to_equal "My App"
```

</details>

#### sets custom theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("btt_root2", "panel")
val tree = build_tree_with_title(root, "App", "light")
expect tree.theme to_equal "light"
```

</details>

#### preserves root node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("btt_root3", "panel")
val tree = build_tree_with_title(root, "Title", "monokai")
expect tree.root.id to_equal "btt_root3"
```

</details>

### Widget modifiers

#### with_flex

#### sets flex property

1. var node = WidgetNode new
2. node = with flex
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("flex1", "panel")
node = with_flex(node, 2)
expect node.get_prop("flex") to_equal "2"
```

</details>

#### with_width

#### sets width property

1. var node = WidgetNode new
2. node = with width
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("width1", "panel")
node = with_width(node, 100)
expect node.get_prop("width") to_equal "100"
```

</details>

#### with_height

#### sets height property

1. var node = WidgetNode new
2. node = with height
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("height1", "panel")
node = with_height(node, 50)
expect node.get_prop("height") to_equal "50"
```

</details>

#### chaining modifiers

#### applies multiple modifiers

1. var node = WidgetNode new
2. node = with flex
3. node = with width
4. node = with height
5. expect node get prop
6. expect node get prop
7. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("chain1", "panel")
node = with_flex(node, 1)
node = with_width(node, 200)
node = with_height(node, 80)
expect node.get_prop("flex") to_equal "1"
expect node.get_prop("width") to_equal "200"
expect node.get_prop("height") to_equal "80"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Container builders
- Leaf widget builders
- Composite widget builders
- Tree builders
- Widget modifiers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

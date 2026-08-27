# Builder Specification

> Tests covering Container builders, Leaf widget builders, Composite widget builders, Tree builders, Widget modifiers.

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

- creates panel with vbox layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates panel with vbox layout")
val c1 = WidgetNode.new("col_child1", "text")
val c2 = WidgetNode.new("col_child2", "text")
val col = column("col1", [c1, c2])
expect col.kind to_equal "panel"
expect col.layout to_equal "vbox"
```

</details>

#### has correct child count

- has correct child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct child count")
val c1 = WidgetNode.new("col2_a", "text")
val c2 = WidgetNode.new("col2_b", "text")
val col = column("col2", [c1, c2])
expect col.child_count() to_equal 2
```

</details>

#### creates empty column with no children

- creates empty column with no children


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty column with no children")
val col = column("col_empty", [])
expect col.kind to_equal "panel"
expect col.child_count() to_equal 0
```

</details>

#### row

#### creates panel with hbox layout

- creates panel with hbox layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates panel with hbox layout")
val c1 = WidgetNode.new("row_child1", "text")
val r = row("row1", [c1])
expect r.kind to_equal "panel"
expect r.layout to_equal "hbox"
```

</details>

#### has correct child count

- has correct child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct child count")
val c1 = WidgetNode.new("row2_a", "text")
val c2 = WidgetNode.new("row2_b", "text")
val c3 = WidgetNode.new("row2_c", "text")
val r = row("row2", [c1, c2, c3])
expect r.child_count() to_equal 3
```

</details>

#### grid

#### creates panel with grid layout

- creates panel with grid layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates panel with grid layout")
val c1 = WidgetNode.new("grid_child1", "text")
val g = builder.grid("grid1", [c1])
expect g.kind to_equal "panel"
expect g.layout to_equal "grid"
```

</details>

#### has correct child count

- has correct child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct child count")
val c1 = WidgetNode.new("grid2_a", "text")
val c2 = WidgetNode.new("grid2_b", "text")
val g = builder.grid("grid2", [c1, c2])
expect g.child_count() to_equal 2
```

</details>

#### panel

#### creates panel with title prop

- creates panel with title prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates panel with title prop")
val child = WidgetNode.new("pan_child", "text")
val p = panel("pan1", "My Panel", [child])
expect p.kind to_equal "panel"
expect p.get_prop("title") to_equal "My Panel"
```

</details>

#### uses vbox layout

- uses vbox layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses vbox layout")
val p = panel("pan2", "Title", [])
expect p.layout to_equal "vbox"
```

</details>

#### has children

- has children


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has children")
val c1 = WidgetNode.new("pan3_a", "text")
val c2 = WidgetNode.new("pan3_b", "button")
val p = panel("pan3", "Container", [c1, c2])
expect p.child_count() to_equal 2
```

</details>

### Leaf widget builders

#### text_widget

#### creates text with content prop

- creates text with content prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates text with content prop")
val tw = text_widget("tw1", "Hello World")
expect tw.kind to_equal "text"
expect tw.get_prop("content") to_equal "Hello World"
```

</details>

#### handles empty content

- handles empty content


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty content")
val tw = text_widget("tw2", "")
expect tw.get_prop("content") to_equal ""
```

</details>

#### label

#### creates text with label prop

- creates text with label prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates text with label prop")
val lbl = label("lbl1", "Username:")
expect lbl.kind to_equal "text"
expect lbl.get_prop("label") to_equal "Username:"
```

</details>

#### input

#### creates input with placeholder prop

- creates input with placeholder prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates input with placeholder prop")
val inp = text_input("inp1", "Enter text...")
expect inp.kind to_equal "input"
expect inp.get_prop("placeholder") to_equal "Enter text..."
```

</details>

#### button

#### creates button with label and action props

- creates button with label and action props


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates button with label and action props")
val btn = button("btn1", "Click Me", "submit")
expect btn.kind to_equal "button"
expect btn.get_prop("label") to_equal "Click Me"
expect btn.get_prop("action") to_equal "submit"
```

</details>

#### checkbox

#### creates checked checkbox

- creates checked checkbox


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates checked checkbox")
val cb = checkbox("cb1", "Accept Terms", true)
expect cb.kind to_equal "checkbox"
expect cb.get_prop("label") to_equal "Accept Terms"
expect cb.get_prop("checked") to_equal "true"
```

</details>

#### creates unchecked checkbox

- creates unchecked checkbox


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates unchecked checkbox")
val cb = checkbox("cb2", "Subscribe", false)
expect cb.get_prop("checked") to_equal "false"
```

</details>

#### text_field

#### creates textfield with value and placeholder

- creates textfield with value and placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates textfield with value and placeholder")
val tf = text_field("tf1", "initial", "Type here")
expect tf.kind to_equal "textfield"
expect tf.get_prop("value") to_equal "initial"
expect tf.get_prop("placeholder") to_equal "Type here"
```

</details>

#### image

#### creates image with src and alt

- creates image with src and alt


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates image with src and alt")
val img = image("img1", "https://example.com/pic.png", "A photo")
expect img.kind to_equal "image"
expect img.get_prop("src") to_equal "https://example.com/pic.png"
expect img.get_prop("alt") to_equal "A photo"
```

</details>

#### divider

#### creates divider widget

- creates divider widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates divider widget")
val div = divider("div1")
expect div.kind to_equal "divider"
```

</details>

#### progress

#### creates progress bar with value

- creates progress bar with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates progress bar with value")
val pb = progress("pb1", 75)
expect pb.kind to_equal "progress"
expect pb.get_prop("value") to_equal "75"
```

</details>

#### creates progress bar with zero

- creates progress bar with zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates progress bar with zero")
val pb = progress("pb2", 0)
expect pb.get_prop("value") to_equal "0"
```

</details>

### Composite widget builders

#### dropdown

#### creates dropdown with option children

- creates dropdown with option children


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates dropdown with option children")
val dd = dropdown("dd1", ["Apple", "Banana"])
expect dd.kind to_equal "dropdown"
expect dd.child_count() to_equal 2
```

</details>

#### option children have label props

- option children have label props


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option children have label props")
val dd = dropdown("dd2", ["Red", "Green", "Blue"])
val first = dd.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "Red"
```

</details>

#### creates empty dropdown with no items

- creates empty dropdown with no items


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty dropdown with no items")
val dd = dropdown("dd3", [])
expect dd.child_count() to_equal 0
```

</details>

#### menubar

#### creates menubar with text children

- creates menubar with text children


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates menubar with text children")
val mb = menubar("mb1", ["File", "Edit"])
expect mb.kind to_equal "menubar"
expect mb.child_count() to_equal 2
```

</details>

#### menu children have label props

- menu children have label props


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("menu children have label props")
val mb = menubar("mb2", ["View", "Help"])
val first = mb.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "View"
```

</details>

#### statusbar

#### creates statusbar with left and right props

- creates statusbar with left and right props


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates statusbar with left and right props")
val sb = statusbar("sb1", "Ready", "Ln 42")
expect sb.kind to_equal "statusbar"
expect sb.get_prop("left") to_equal "Ready"
expect sb.get_prop("right") to_equal "Ln 42"
```

</details>

#### tabs

#### creates tabs with labeled children

- creates tabs with labeled children


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates tabs with labeled children")
val tb = tabs("tb1", ["Tab1", "Tab2"])
expect tb.kind to_equal "tabs"
expect tb.child_count() to_equal 2
```

</details>

#### tab children have label props

- tab children have label props


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tab children have label props")
val tb = tabs("tb2", ["Home", "Settings", "About"])
val second = tb.child_at(1)
expect second != nil to_equal true
expect second.get_prop("label") to_equal "Settings"
```

</details>

#### list_widget

#### creates list with item children

- creates list with item children


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates list with item children")
val lw = list_widget("lw1", ["Alpha", "Beta", "Gamma"])
expect lw.kind to_equal "list"
expect lw.child_count() to_equal 3
```

</details>

#### item children have label props

- item children have label props


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("item children have label props")
val lw = list_widget("lw2", ["First", "Second"])
val first = lw.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "First"
```

</details>

#### dialog

#### creates dialog with title prop

- creates dialog with title prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates dialog with title prop")
val dlg = dialog("dlg1", "Confirm", [])
expect dlg.kind to_equal "dialog"
expect dlg.get_prop("title") to_equal "Confirm"
```

</details>

#### dialog has vbox layout

- dialog has vbox layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dialog has vbox layout")
val dlg = dialog("dlg2", "Alert", [])
expect dlg.layout to_equal "vbox"
```

</details>

#### tooltip

#### creates tooltip with content and target

- creates tooltip with content and target


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates tooltip with content and target")
val tt = tooltip("tt1", "Help text", "btn_target")
expect tt.kind to_equal "tooltip"
expect tt.get_prop("content") to_equal "Help text"
expect tt.get_prop("target") to_equal "btn_target"
```

</details>

### Tree builders

#### build_tree

#### wraps root in UITree

- wraps root in UITree


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps root in UITree")
val root = WidgetNode.new("bt_root", "panel")
val tree = build_tree(root)
expect tree.root.id to_equal "bt_root"
```

</details>

#### uses default title

- uses default title


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses default title")
val root = WidgetNode.new("bt_root2", "panel")
val tree = build_tree(root)
expect tree.title to_equal "Simple UI"
```

</details>

#### uses default theme

- uses default theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses default theme")
val root = WidgetNode.new("bt_root3", "panel")
val tree = build_tree(root)
expect tree.theme to_equal "dark"
```

</details>

#### build_tree_with_title

#### sets custom title

- sets custom title


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets custom title")
val root = WidgetNode.new("btt_root1", "panel")
val tree = build_tree_with_title(root, "My App", "dark")
expect tree.title to_equal "My App"
```

</details>

#### sets custom theme

- sets custom theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets custom theme")
val root = WidgetNode.new("btt_root2", "panel")
val tree = build_tree_with_title(root, "App", "light")
expect tree.theme to_equal "light"
```

</details>

#### preserves root node

- preserves root node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves root node")
val root = WidgetNode.new("btt_root3", "panel")
val tree = build_tree_with_title(root, "Title", "monokai")
expect tree.root.id to_equal "btt_root3"
```

</details>

### Widget modifiers

#### with_flex

#### sets flex property

- sets flex property


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets flex property")
var node = WidgetNode.new("flex1", "panel")
node = with_flex(node, 2)
expect node.get_prop("flex") to_equal "2"
```

</details>

#### with_width

#### sets width property

- sets width property


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets width property")
var node = WidgetNode.new("width1", "panel")
node = with_width(node, 100)
expect node.get_prop("width") to_equal "100"
```

</details>

#### with_height

#### sets height property

- sets height property


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets height property")
var node = WidgetNode.new("height1", "panel")
node = with_height(node, 50)
expect node.get_prop("height") to_equal "50"
```

</details>

#### chaining modifiers

#### applies multiple modifiers

- applies multiple modifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies multiple modifiers")
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
| Source | `test/unit/app/ui/builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Container builders, Leaf widget builders, Composite widget builders, Tree builders, Widget modifiers.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3578502def587d1cfb7e9c8099376f72076c32fd8e3d3de0b580427b10f1484d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3578502def587d1cfb7e9c8099376f72076c32fd8e3d3de0b580427b10f1484d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3578502def587d1cfb7e9c8099376f72076c32fd8e3d3de0b580427b10f1484d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/builder_spec.spl
mirror: doc/06_spec/unit/app/ui/builder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/builder_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates panel with vbox layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/builder_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct child count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/builder_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty column with no children' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

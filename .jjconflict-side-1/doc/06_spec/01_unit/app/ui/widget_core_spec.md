# Widget Core Specification

> <details>

<!-- sdn-diagram:id=widget_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_core_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Core Specification

## Scenarios

### WidgetNode creation

#### creates node with correct id and kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("w1", "panel")
expect node.id to_equal "w1"
expect node.kind to_equal "panel"
```

</details>

#### defaults layout to vbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("w2", "text")
expect node.layout to_equal "vbox"
```

</details>

#### defaults visible to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("w3", "button")
expect node.visible to_equal true
```

</details>

#### defaults focused to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("w4", "input")
expect node.focused to_equal false
```

</details>

#### starts with empty props

1. expect keys len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("w5", "text")
val keys = node.prop_keys()
expect keys.len() to_equal 0
```

</details>

### WidgetNode properties

#### set_prop and get_prop

#### adds a new property and retrieves it

1. var node = WidgetNode new
2. node = node set prop
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("p1", "text")
node = node.set_prop("color", "red")
expect node.get_prop("color") to_equal "red"
```

</details>

#### overwrites an existing property

1. var node = WidgetNode new
2. node = node set prop
3. node = node set prop
4. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("p2", "text")
node = node.set_prop("color", "red")
node = node.set_prop("color", "blue")
expect node.get_prop("color") to_equal "blue"
```

</details>

#### preserves other properties when overwriting

1. var node = WidgetNode new
2. node = node set prop
3. node = node set prop
4. node = node set prop
5. expect node get prop
6. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("p3", "text")
node = node.set_prop("color", "red")
node = node.set_prop("size", "12")
node = node.set_prop("color", "blue")
expect node.get_prop("color") to_equal "blue"
expect node.get_prop("size") to_equal "12"
```

</details>

#### supports multiple properties

1. var node = WidgetNode new
2. node = node set prop
3. node = node set prop
4. node = node set prop
5. expect node get prop
6. expect node get prop
7. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("p4", "panel")
node = node.set_prop("title", "Main")
node = node.set_prop("border", "single")
node = node.set_prop("bg", "black")
expect node.get_prop("title") to_equal "Main"
expect node.get_prop("border") to_equal "single"
expect node.get_prop("bg") to_equal "black"
```

</details>

#### has_prop

#### returns true for existing property

1. var node = WidgetNode new
2. node = node set prop
3. expect node has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("h1", "text")
node = node.set_prop("label", "Hello")
expect node.has_prop("label") to_equal true
```

</details>

#### returns false for missing property

1. expect node has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("h2", "text")
expect node.has_prop("nonexistent") to_equal false
```

</details>

#### get_prop for missing key

#### returns empty string for missing property

1. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("g1", "text")
expect node.get_prop("missing") to_equal ""
```

</details>

#### prop_keys

#### returns all property keys

1. var node = WidgetNode new
2. node = node set prop
3. node = node set prop
4. node = node set prop
5. expect keys len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("k1", "panel")
node = node.set_prop("alpha", "1")
node = node.set_prop("beta", "2")
node = node.set_prop("gamma", "3")
val keys = node.prop_keys()
expect keys.len() to_equal 3
expect keys to_contain "alpha"
expect keys to_contain "beta"
expect keys to_contain "gamma"
```

</details>

### WidgetNode children

#### add_child and children

#### registers child and retrieves it

1. var parent = WidgetNode new
2. parent = parent add child
3. expect kids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = WidgetNode.new("parent1", "panel")
val child = WidgetNode.new("child1", "text")
parent = parent.add_child(child)
val kids = parent.children()
expect kids.len() to_equal 1
```

</details>

#### retrieves children with correct ids

1. var parent = WidgetNode new
2. parent = parent add child
3. parent = parent add child
4. expect kids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = WidgetNode.new("parent2", "panel")
val c1 = WidgetNode.new("kid_a", "text")
val c2 = WidgetNode.new("kid_b", "button")
parent = parent.add_child(c1)
parent = parent.add_child(c2)
val kids = parent.children()
expect kids.len() to_equal 2
```

</details>

#### child_count

#### returns zero for node with no children

1. expect node child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("cc0", "text")
expect node.child_count() to_equal 0
```

</details>

#### returns correct count after adding children

1. var parent = WidgetNode new
2. parent = parent add child
3. parent = parent add child
4. parent = parent add child
5. expect parent child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = WidgetNode.new("cc1", "panel")
val c1 = WidgetNode.new("cc1_a", "text")
val c2 = WidgetNode.new("cc1_b", "text")
val c3 = WidgetNode.new("cc1_c", "text")
parent = parent.add_child(c1)
parent = parent.add_child(c2)
parent = parent.add_child(c3)
expect parent.child_count() to_equal 3
```

</details>

#### child_at

#### returns first child at index 0

1. var parent = WidgetNode new
2. parent = parent add child
3. parent = parent add child


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = WidgetNode.new("ca1", "panel")
val c1 = WidgetNode.new("ca1_first", "text")
val c2 = WidgetNode.new("ca1_second", "button")
parent = parent.add_child(c1)
parent = parent.add_child(c2)
val first = parent.child_at(0)
expect first != nil to_equal true
expect first.id to_equal "ca1_first"
```

</details>

#### returns nil for negative index

1. var parent = WidgetNode new
2. parent = parent add child


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = WidgetNode.new("ca2", "panel")
val c1 = WidgetNode.new("ca2_child", "text")
parent = parent.add_child(c1)
val result = parent.child_at(-1)
expect result == nil to_equal true
```

</details>

### WidgetNode search

#### find_by_id

#### finds self when id matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("find_self", "panel")
val found = node.find_by_id("find_self")
expect found != nil to_equal true
expect found.id to_equal "find_self"
```

</details>

#### finds a child by id

1. var parent = WidgetNode new
2. parent = parent add child


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = WidgetNode.new("find_parent", "panel")
val child = WidgetNode.new("find_child", "text")
parent = parent.add_child(child)
val found = parent.find_by_id("find_child")
expect found != nil to_equal true
expect found.id to_equal "find_child"
```

</details>

#### returns nil for missing id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("find_miss", "panel")
val found = node.find_by_id("does_not_exist")
expect found == nil to_equal true
```

</details>

#### collect_ids

#### returns own id for leaf node

1. expect ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = WidgetNode.new("leaf1", "text")
val ids = node.collect_ids()
expect ids.len() to_equal 1
expect ids to_contain "leaf1"
```

</details>

#### returns all descendant ids

1. var root = WidgetNode new
2. root = root add child
3. root = root add child
4. expect ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = WidgetNode.new("root_ids", "panel")
val c1 = WidgetNode.new("ids_c1", "text")
val c2 = WidgetNode.new("ids_c2", "button")
root = root.add_child(c1)
root = root.add_child(c2)
val ids = root.collect_ids()
expect ids.len() to_equal 3
expect ids to_contain "root_ids"
expect ids to_contain "ids_c1"
expect ids to_contain "ids_c2"
```

</details>

### WidgetNode layout and visibility

#### set_layout changes layout

1. var node = WidgetNode new
2. node = node set layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("lay1", "panel")
expect node.layout to_equal "vbox"
node = node.set_layout("hbox")
expect node.layout to_equal "hbox"
```

</details>

#### set_visible sets visible to false

1. var node = WidgetNode new
2. node = node set visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("vis1", "panel")
expect node.visible to_equal true
node = node.set_visible(false)
expect node.visible to_equal false
```

</details>

#### set_visible sets visible back to true

1. var node = WidgetNode new
2. node = node set visible
3. node = node set visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = WidgetNode.new("vis2", "panel")
node = node.set_visible(false)
node = node.set_visible(true)
expect node.visible to_equal true
```

</details>

### UITree

#### creates tree with default title

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("tree_root1", "panel")
val tree = UITree.new(root)
expect tree.title to_equal "Simple UI"
```

</details>

#### creates tree with default theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("tree_root2", "panel")
val tree = UITree.new(root)
expect tree.theme to_equal "dark"
```

</details>

#### stores the root node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("tree_root3", "panel")
val tree = UITree.new(root)
expect tree.root.id to_equal "tree_root3"
```

</details>

#### find_widget finds root

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("tree_find1", "panel")
val tree = UITree.new(root)
val found = tree.find_widget("tree_find1")
expect found != nil to_equal true
expect found.id to_equal "tree_find1"
```

</details>

#### all_widget_ids returns all ids

1. var root = WidgetNode new
2. root = root add child
3. expect ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = WidgetNode.new("tree_all_root", "panel")
val child = WidgetNode.new("tree_all_child", "text")
root = root.add_child(child)
val tree = UITree.new(root)
val ids = tree.all_widget_ids()
expect ids.len() to_equal 2
expect ids to_contain "tree_all_root"
expect ids to_contain "tree_all_child"
```

</details>

### UIState

#### sets initial focus to first widget id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("state_root", "panel")
val tree = UITree.new(root)
val state = UIState.new(tree)
expect state.focused_id to_equal "state_root"
```

</details>

#### starts in Normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("state_mode", "panel")
val tree = UITree.new(root)
val state = UIState.new(tree)
expect state.mode to_equal UIMode.Normal
```

</details>

#### mode_name returns NORMAL for Normal mode

1. expect state mode name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("state_name", "panel")
val tree = UITree.new(root)
val state = UIState.new(tree)
expect state.mode_name() to_equal "NORMAL"
```

</details>

#### starts with empty command buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = WidgetNode.new("state_buf", "panel")
val tree = UITree.new(root)
val state = UIState.new(tree)
expect state.command_buffer to_equal ""
```

</details>

### WidgetRect

#### creates rect with correct values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = WidgetRect.new("rect1", 10, 20, 100, 50)
expect rect.id to_equal "rect1"
expect rect.x to_equal 10
expect rect.y to_equal 20
expect rect.w to_equal 100
expect rect.h to_equal 50
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WidgetNode creation
- WidgetNode properties
- WidgetNode children
- WidgetNode search
- WidgetNode layout and visibility
- UITree
- UIState
- WidgetRect

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

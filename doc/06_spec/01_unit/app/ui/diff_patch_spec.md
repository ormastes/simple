# Diff Patch Specification

> 1. expect patches len

<!-- sdn-diagram:id=diff_patch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diff_patch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diff_patch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diff_patch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diff Patch Specification

## Scenarios

### diff_trees identical

#### produces empty patch list for identical trees

1. expect patches len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_tree = WidgetNode.new("id1", "text")
val new_tree = WidgetNode.new("id1", "text")
val patches = diff_trees(old_tree, new_tree)
expect patches.len() to_equal 0
```

</details>

### diff_trees property changes

#### produces UpdateProp patch for changed property

1. var old node = WidgetNode new
2. old node = old node set prop
3. var new node = WidgetNode new
4. new node = new node set prop
5. expect patches len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var old_node = WidgetNode.new("prop1", "text")
old_node = old_node.set_prop("content", "Hello")
var new_node = WidgetNode.new("prop1", "text")
new_node = new_node.set_prop("content", "World")
val patches = diff_trees(old_node, new_node)
expect patches.len() to_equal 1
val patch = patches[0]
expect patch.kind to_equal PatchKind.UpdateProp
expect patch.prop_key to_equal "content"
expect patch.prop_value to_equal "World"
```

</details>

#### produces RemoveProp patch for removed property

1. var old node = WidgetNode new
2. old node = old node set prop
3. old node = old node set prop
4. var new node = WidgetNode new
5. new node = new node set prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var old_node = WidgetNode.new("prop2", "text")
old_node = old_node.set_prop("content", "Hello")
old_node = old_node.set_prop("color", "red")
var new_node = WidgetNode.new("prop2", "text")
new_node = new_node.set_prop("content", "Hello")
# "color" prop is absent in new_node
val patches = diff_trees(old_node, new_node)
var found_remove = false
for patch in patches:
    if patch.kind == PatchKind.RemoveProp and patch.prop_key == "color":
        found_remove = true
expect found_remove to_equal true
```

</details>

#### produces UpdateProp patch for added property

1. var old node = WidgetNode new
2. old node = old node set prop
3. var new node = WidgetNode new
4. new node = new node set prop
5. new node = new node set prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var old_node = WidgetNode.new("prop3", "text")
old_node = old_node.set_prop("content", "Hello")
var new_node = WidgetNode.new("prop3", "text")
new_node = new_node.set_prop("content", "Hello")
new_node = new_node.set_prop("color", "blue")
val patches = diff_trees(old_node, new_node)
var found_update = false
for patch in patches:
    if patch.kind == PatchKind.UpdateProp and patch.prop_key == "color":
        found_update = true
        expect patch.prop_value to_equal "blue"
expect found_update to_equal true
```

</details>

### diff_trees kind changes

#### produces ReplaceNode patch for changed kind

1. expect patches len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_node = WidgetNode.new("kind1", "text")
val new_node = WidgetNode.new("kind1", "button")
val patches = diff_trees(old_node, new_node)
expect patches.len() to_equal 1
expect patches[0].kind to_equal PatchKind.ReplaceNode
```

</details>

### diff_trees layout changes

#### produces UpdateLayout patch for changed layout

1. var old node = WidgetNode new
2. old node = old node set layout
3. var new node = WidgetNode new
4. new node = new node set layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var old_node = WidgetNode.new("lay1", "panel")
old_node = old_node.set_layout("vbox")
var new_node = WidgetNode.new("lay1", "panel")
new_node = new_node.set_layout("hbox")
val patches = diff_trees(old_node, new_node)
var found_layout = false
for patch in patches:
    if patch.kind == PatchKind.UpdateLayout:
        found_layout = true
expect found_layout to_equal true
```

</details>

### diff_trees visibility changes

#### produces UpdateVisibility patch for changed visibility

1. var old node = WidgetNode new
2. var new node = WidgetNode new
3. new node = new node set visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var old_node = WidgetNode.new("vis1", "panel")
var new_node = WidgetNode.new("vis1", "panel")
new_node = new_node.set_visible(false)
val patches = diff_trees(old_node, new_node)
var found_vis = false
for patch in patches:
    if patch.kind == PatchKind.UpdateVisibility:
        found_vis = true
expect found_vis to_equal true
```

</details>

### diff_trees child changes

#### produces InsertChild patch for added child

1. var new node = WidgetNode new
2. new node = new node add child


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_node = WidgetNode.new("par1", "panel")
var new_node = WidgetNode.new("par1", "panel")
val child = WidgetNode.new("par1_child", "text")
new_node = new_node.add_child(child)
val patches = diff_trees(old_node, new_node)
var found_insert = false
for patch in patches:
    if patch.kind == PatchKind.InsertChild:
        found_insert = true
        expect patch.target_id to_equal "par1_child"
expect found_insert to_equal true
```

</details>

#### produces RemoveChild patch for removed child

1. var old node = WidgetNode new
2. old node = old node add child


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var old_node = WidgetNode.new("par2", "panel")
val child = WidgetNode.new("par2_child", "text")
old_node = old_node.add_child(child)
val new_node = WidgetNode.new("par2", "panel")
val patches = diff_trees(old_node, new_node)
var found_remove = false
for patch in patches:
    if patch.kind == PatchKind.RemoveChild:
        found_remove = true
        expect patch.target_id to_equal "par2_child"
expect found_remove to_equal true
```

</details>

#### produces no patches when children are identical

1. var old node = WidgetNode new
2. old node = old node add child
3. var new node = WidgetNode new
4. new node = new node add child
5. expect patches len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var old_node = WidgetNode.new("par3", "panel")
val child_old = WidgetNode.new("par3_kid", "text")
old_node = old_node.add_child(child_old)
var new_node = WidgetNode.new("par3", "panel")
val child_new = WidgetNode.new("par3_kid", "text")
new_node = new_node.add_child(child_new)
val patches = diff_trees(old_node, new_node)
expect patches.len() to_equal 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/diff_patch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- diff_trees identical
- diff_trees property changes
- diff_trees kind changes
- diff_trees layout changes
- diff_trees visibility changes
- diff_trees child changes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Widget Tree Specification

> 1. expect tw kind name

<!-- sdn-diagram:id=widget_tree_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_tree_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_tree_spec -> common
widget_tree_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_tree_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Tree Specification

## Scenarios

### Tree widget creation

#### creates a widget with kind tree

1. expect tw kind name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tw = tree_widget("tw_create_1", [])
expect tw.kind_name() to_equal "tree"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tw = tree_widget("tw_id_1", [])
expect tw.id to_equal "tw_id_1"
```

</details>

#### has vbox layout

1. expect tw layout name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tw = tree_widget("tw_layout_1", [])
expect tw.layout_name() to_equal "vbox"
```

</details>

#### empty tree has zero children

1. expect tw child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tw = tree_widget("tw_empty_1", [])
expect tw.child_count() to_equal 0
```

</details>

#### tree with one child has child_count 1

1. expect tw child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = tree_leaf("tw_child_leaf_1", "File.txt")
val tw = tree_widget("tw_one_child_1", [leaf])
expect tw.child_count() to_equal 1
```

</details>

#### tree with multiple children has correct count

1. expect tw child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = tree_leaf("tw_mc_1", "A")
val c2 = tree_leaf("tw_mc_2", "B")
val c3 = tree_leaf("tw_mc_3", "C")
val tw = tree_widget("tw_multi_1", [c1, c2, c3])
expect tw.child_count() to_equal 3
```

</details>

### TreeNode widget creation

#### creates a widget with kind treenode

1. expect tn kind name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tn = tree_node("tn_create_1", "Folder", [])
expect tn.kind_name() to_equal "treenode"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tn = tree_node("tn_id_1", "Docs", [])
expect tn.id to_equal "tn_id_1"
```

</details>

#### stores label prop

1. expect tn get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tn = tree_node("tn_label_1", "Documents", [])
expect tn.get_prop("label") to_equal "Documents"
```

</details>

#### defaults expanded to true

1. expect tn get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tn = tree_node("tn_expanded_1", "Folder", [])
expect tn.get_prop("expanded") to_equal "true"
```

</details>

#### tree_node with children has correct child count

1. expect tn child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child1 = tree_leaf("tn_cc_1", "file1.txt")
val child2 = tree_leaf("tn_cc_2", "file2.txt")
val tn = tree_node("tn_children_1", "Docs", [child1, child2])
expect tn.child_count() to_equal 2
```

</details>

#### child is accessible via child_at

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = tree_leaf("tn_at_1", "readme.md")
val tn = tree_node("tn_access_1", "Root", [child])
val retrieved = tn.child_at(0)
expect retrieved != nil to_equal true
expect retrieved.id to_equal "tn_at_1"
```

</details>

### TreeLeaf widget creation

#### creates a widget with kind treenode

1. expect tl kind name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = tree_leaf("tl_create_1", "file.spl")
expect tl.kind_name() to_equal "treenode"
```

</details>

#### stores label prop

1. expect tl get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = tree_leaf("tl_label_1", "readme.md")
expect tl.get_prop("label") to_equal "readme.md"
```

</details>

#### has expanded set to false

1. expect tl get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = tree_leaf("tl_exp_1", "data.csv")
expect tl.get_prop("expanded") to_equal "false"
```

</details>

#### has no children

1. expect tl child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = tree_leaf("tl_no_child_1", "notes.txt")
expect tl.child_count() to_equal 0
```

</details>

### Nested tree structure

#### parent with two children each with sub-children

1. expect tw child count
2. expect first child count
3. expect second child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sub1a = tree_leaf("nest_sub1a", "a.txt")
val sub1b = tree_leaf("nest_sub1b", "b.txt")
val child1 = tree_node("nest_child1", "Folder1", [sub1a, sub1b])

val sub2a = tree_leaf("nest_sub2a", "c.txt")
val child2 = tree_node("nest_child2", "Folder2", [sub2a])

val tw = tree_widget("nest_tree_1", [child1, child2])
expect tw.child_count() to_equal 2

val first = tw.child_at(0)
expect first != nil to_equal true
expect first.child_count() to_equal 2

val second = tw.child_at(1)
expect second != nil to_equal true
expect second.child_count() to_equal 1
```

</details>

#### deeply nested tree preserves structure

1. expect top node get prop
2. expect mid node get prop
3. expect leaf node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deep_leaf = tree_leaf("deep_leaf_1", "deep.txt")
val mid = tree_node("deep_mid_1", "Mid", [deep_leaf])
val top = tree_node("deep_top_1", "Top", [mid])
val tw = tree_widget("deep_tree_1", [top])

val top_node = tw.child_at(0)
expect top_node != nil to_equal true
expect top_node.get_prop("label") to_equal "Top"

val mid_node = top_node.child_at(0)
expect mid_node != nil to_equal true
expect mid_node.get_prop("label") to_equal "Mid"

val leaf_node = mid_node.child_at(0)
expect leaf_node != nil to_equal true
expect leaf_node.get_prop("label") to_equal "deep.txt"
```

</details>

### Tree HTML rendering

#### output contains widget-tree class

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = tree_leaf("html_tree_leaf_1", "file.spl")
val node = tree_widget("html_tree_1", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-tree"
```

</details>

#### output contains tree-root ul

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = tree_leaf("html_tree_leaf_2", "item")
val node = tree_widget("html_tree_2", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "tree-root"
```

</details>

#### output contains tree-node class

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = tree_leaf("html_tree_leaf_3", "item")
val node = tree_widget("html_tree_3", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "tree-node"
```

</details>

#### output contains tree-label span

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = tree_leaf("html_tree_leaf_4", "my_file.spl")
val node = tree_widget("html_tree_4", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "tree-label"
expect html to_contain "my_file.spl"
```

</details>

#### expanded node contains tree-toggle span

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = tree_leaf("html_exp_leaf_1", "child.txt")
val parent = tree_node("html_exp_node_1", "Parent", [child])
val node = tree_widget("html_exp_tree_1", [parent])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "tree-toggle"
```

</details>

#### expanded node has expanded class

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = tree_leaf("html_expclass_leaf_1", "c.txt")
val parent = tree_node("html_expclass_node_1", "Dir", [child])
val node = tree_widget("html_expclass_tree_1", [parent])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "expanded"
```

</details>

#### collapsed node has collapsed class

1. var parent = tree node
2. parent = parent set prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = tree_leaf("html_col_leaf_1", "x.txt")
var parent = tree_node("html_col_node_1", "Archive", [child])
parent = parent.set_prop("expanded", "false")
val node = tree_widget("html_col_tree_1", [parent])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "collapsed"
```

</details>

#### leaf node has leaf class

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = tree_leaf("html_leafclass_1", "single.txt")
val node = tree_widget("html_leafclass_tree_1", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "leaf"
```

</details>

#### focused tree has focused class

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = tree_leaf("html_focus_leaf_1", "f.txt")
val node = tree_widget("html_focus_tree_1", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
expect state.focused_id to_equal "html_focus_tree_1"
val html = render_html_widget(node, state)
expect html to_contain "focused"
```

</details>

#### output includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tree_widget("html_id_tree_1", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "id=\"html_id_tree_1\""
```

</details>

#### toggle data-action references node id

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = tree_leaf("html_toggle_leaf_1", "f.spl")
val parent = tree_node("html_toggle_node_1", "Src", [child])
val node = tree_widget("html_toggle_tree_1", [parent])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-action=\"toggle_html_toggle_node_1\""
```

</details>

### child_count works for tree nodes

#### tree_node child_count returns correct value

1. expect tn child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = tree_leaf("cc_a_1", "a")
val b = tree_leaf("cc_b_1", "b")
val c = tree_leaf("cc_c_1", "c")
val tn = tree_node("cc_node_1", "Dir", [a, b, c])
expect tn.child_count() to_equal 3
```

</details>

#### tree_leaf child_count returns zero

1. expect tl child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = tree_leaf("cc_leaf_1", "x")
expect tl.child_count() to_equal 0
```

</details>

#### tree_widget child_count returns number of top-level nodes

1. expect tw child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n1 = tree_node("cc_tw_n1", "D1", [])
val n2 = tree_leaf("cc_tw_n2", "f1")
val tw = tree_widget("cc_tw_1", [n1, n2])
expect tw.child_count() to_equal 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_tree_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tree widget creation
- TreeNode widget creation
- TreeLeaf widget creation
- Nested tree structure
- Tree HTML rendering
- child_count works for tree nodes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

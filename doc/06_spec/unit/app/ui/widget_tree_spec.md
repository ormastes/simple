# Widget Tree Specification

> Tests covering Tree widget creation, TreeNode widget creation, TreeLeaf widget creation, Nested tree structure, Tree HTML rendering, child_count works for tree nodes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Tree Specification

## Scenarios

### Tree widget creation

#### creates a widget with kind tree

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a widget with kind tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a widget with kind tree")
val tw = tree_widget("tw_create_1", [])
expect tw.kind_name() to_equal "tree"
```

</details>

#### assigns the correct id

- assigns the correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the correct id")
val tw = tree_widget("tw_id_1", [])
expect tw.id to_equal "tw_id_1"
```

</details>

#### has vbox layout

- has vbox layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has vbox layout")
val tw = tree_widget("tw_layout_1", [])
expect tw.layout_name() to_equal "vbox"
```

</details>

#### empty tree has zero children

- empty tree has zero children


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty tree has zero children")
val tw = tree_widget("tw_empty_1", [])
expect tw.child_count() to_equal 0
```

</details>

#### tree with one child has child_count 1

- tree with one child has child_count 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree with one child has child_count 1")
val leaf = tree_leaf("tw_child_leaf_1", "File.txt")
val tw = tree_widget("tw_one_child_1", [leaf])
expect tw.child_count() to_equal 1
```

</details>

#### tree with multiple children has correct count

- tree with multiple children has correct count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree with multiple children has correct count")
val c1 = tree_leaf("tw_mc_1", "A")
val c2 = tree_leaf("tw_mc_2", "B")
val c3 = tree_leaf("tw_mc_3", "C")
val tw = tree_widget("tw_multi_1", [c1, c2, c3])
expect tw.child_count() to_equal 3
```

</details>

### TreeNode widget creation

#### creates a widget with kind treenode

- creates a widget with kind treenode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a widget with kind treenode")
val tn = tree_node("tn_create_1", "Folder", [])
expect tn.kind_name() to_equal "treenode"
```

</details>

#### assigns the correct id

- assigns the correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the correct id")
val tn = tree_node("tn_id_1", "Docs", [])
expect tn.id to_equal "tn_id_1"
```

</details>

#### stores label prop

- stores label prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores label prop")
val tn = tree_node("tn_label_1", "Documents", [])
expect tn.get_prop("label") to_equal "Documents"
```

</details>

#### defaults expanded to true

- defaults expanded to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults expanded to true")
val tn = tree_node("tn_expanded_1", "Folder", [])
expect tn.get_prop("expanded") to_equal "true"
```

</details>

#### tree_node with children has correct child count

- tree_node with children has correct child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree_node with children has correct child count")
val child1 = tree_leaf("tn_cc_1", "file1.txt")
val child2 = tree_leaf("tn_cc_2", "file2.txt")
val tn = tree_node("tn_children_1", "Docs", [child1, child2])
expect tn.child_count() to_equal 2
```

</details>

#### child is accessible via child_at

- child is accessible via child_at


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("child is accessible via child_at")
val child = tree_leaf("tn_at_1", "readme.md")
val tn = tree_node("tn_access_1", "Root", [child])
val retrieved = tn.child_at(0)
expect retrieved != nil to_equal true
expect retrieved.id to_equal "tn_at_1"
```

</details>

### TreeLeaf widget creation

#### creates a widget with kind treenode

- creates a widget with kind treenode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a widget with kind treenode")
val tl = tree_leaf("tl_create_1", "file.spl")
expect tl.kind_name() to_equal "treenode"
```

</details>

#### stores label prop

- stores label prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores label prop")
val tl = tree_leaf("tl_label_1", "readme.md")
expect tl.get_prop("label") to_equal "readme.md"
```

</details>

#### has expanded set to false

- has expanded set to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has expanded set to false")
val tl = tree_leaf("tl_exp_1", "data.csv")
expect tl.get_prop("expanded") to_equal "false"
```

</details>

#### has no children

- has no children


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no children")
val tl = tree_leaf("tl_no_child_1", "notes.txt")
expect tl.child_count() to_equal 0
```

</details>

### Nested tree structure

#### parent with two children each with sub-children

- parent with two children each with sub-children


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parent with two children each with sub-children")
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

- deeply nested tree preserves structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deeply nested tree preserves structure")
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

- output contains widget-tree class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains widget-tree class")
val leaf = tree_leaf("html_tree_leaf_1", "file.spl")
val node = tree_widget("html_tree_1", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-tree"
```

</details>

#### output contains tree-root ul

- output contains tree-root ul


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains tree-root ul")
val leaf = tree_leaf("html_tree_leaf_2", "item")
val node = tree_widget("html_tree_2", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "tree-root"
```

</details>

#### output contains tree-node class

- output contains tree-node class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains tree-node class")
val leaf = tree_leaf("html_tree_leaf_3", "item")
val node = tree_widget("html_tree_3", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "tree-node"
```

</details>

#### output contains tree-label span

- output contains tree-label span


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains tree-label span")
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

- expanded node contains tree-toggle span


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expanded node contains tree-toggle span")
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

- expanded node has expanded class


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expanded node has expanded class")
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

- collapsed node has collapsed class


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collapsed node has collapsed class")
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

- leaf node has leaf class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaf node has leaf class")
val leaf = tree_leaf("html_leafclass_1", "single.txt")
val node = tree_widget("html_leafclass_tree_1", [leaf])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "leaf"
```

</details>

#### focused tree has focused class

- focused tree has focused class


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("focused tree has focused class")
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

- output includes widget id attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output includes widget id attribute")
val node = tree_widget("html_id_tree_1", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "id=\"html_id_tree_1\""
```

</details>

#### toggle data-action references node id

- toggle data-action references node id


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("toggle data-action references node id")
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

- tree_node child_count returns correct value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree_node child_count returns correct value")
val a = tree_leaf("cc_a_1", "a")
val b = tree_leaf("cc_b_1", "b")
val c = tree_leaf("cc_c_1", "c")
val tn = tree_node("cc_node_1", "Dir", [a, b, c])
expect tn.child_count() to_equal 3
```

</details>

#### tree_leaf child_count returns zero

- tree_leaf child_count returns zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree_leaf child_count returns zero")
val tl = tree_leaf("cc_leaf_1", "x")
expect tl.child_count() to_equal 0
```

</details>

#### tree_widget child_count returns number of top-level nodes

- tree_widget child_count returns number of top-level nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree_widget child_count returns number of top-level nodes")
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
| Source | `test/unit/app/ui/widget_tree_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Tree widget creation, TreeNode widget creation, TreeLeaf widget creation, Nested tree structure, Tree HTML rendering, child_count works for tree nodes.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e9a6fc633aed931319616e2741b9ee1eeaba810668c3fe67134c688818e78b40`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9a6fc633aed931319616e2741b9ee1eeaba810668c3fe67134c688818e78b40`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9a6fc633aed931319616e2741b9ee1eeaba810668c3fe67134c688818e78b40`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/widget_tree_spec.spl
mirror: doc/06_spec/unit/app/ui/widget_tree_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/widget_tree_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/widget_tree_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/widget_tree_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a widget with kind tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_tree_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns the correct id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_tree_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has vbox layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Blink DOM Node Specification

> Tests for the Blink-style DOM Node stub — the base class of Blink's DOM tree. Covers DocumentNode root initialization, Element + Text creation, parent/child pointer updates on append_child, sibling chain linkage, and attribute set/get/replace semantics.

<!-- sdn-diagram:id=dom_node_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dom_node_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dom_node_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dom_node_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink DOM Node Specification

Tests for the Blink-style DOM Node stub — the base class of Blink's DOM tree. Covers DocumentNode root initialization, Element + Text creation, parent/child pointer updates on append_child, sibling chain linkage, and attribute set/get/replace semantics.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/01_unit/lib/blink/dom_node_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Blink-style DOM Node stub — the base class of Blink's DOM tree.
Covers DocumentNode root initialization, Element + Text creation, parent/child
pointer updates on append_child, sibling chain linkage, and attribute
set/get/replace semantics.

## Scenarios

### dom_tree_new

#### has root DocumentNode at id 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
expect(tree.root_id).to_equal(0)
val root_opt = tree.get_node(0)
val root = root_opt.unwrap()
val is_doc = root.node_type == NodeType.DocumentNode
expect(is_doc).to_equal(true)
```

</details>

### create_element

#### returns new id, node_type is Element

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
val elem_id = tree.create_element("div")
expect(elem_id).to_be_greater_than(0)
val node = tree.get_node(elem_id).unwrap()
val is_elem = node.node_type == NodeType.Element
expect(is_elem).to_equal(true)
expect(node.tag_name).to_equal("div")
```

</details>

### create_text

#### returns new id, text_content is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
val text_id = tree.create_text("hello world")
expect(text_id).to_be_greater_than(0)
val node = tree.get_node(text_id).unwrap()
val is_text = node.node_type == NodeType.Text
expect(is_text).to_equal(true)
expect(node.text_content).to_equal("hello world")
```

</details>

### append_child

#### parent's first_child is set

1. tree append child
   - Expected: root.first_child equals `elem_id`
   - Expected: child.parent equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
val elem_id = tree.create_element("p")
tree.append_child(0, elem_id)
val root = tree.get_node(0).unwrap()
expect(root.first_child).to_equal(elem_id)
val child = tree.get_node(elem_id).unwrap()
expect(child.parent).to_equal(0)
```

</details>

#### two children form sibling chain

1. tree append child
2. tree append child
   - Expected: a.next_sibling equals `b_id`
   - Expected: b.prev_sibling equals `a_id`
   - Expected: b.next_sibling equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
val a_id = tree.create_element("a")
val b_id = tree.create_element("b")
tree.append_child(0, a_id)
tree.append_child(0, b_id)
val a = tree.get_node(a_id).unwrap()
val b = tree.get_node(b_id).unwrap()
expect(a.next_sibling).to_equal(b_id)
expect(b.prev_sibling).to_equal(a_id)
expect(b.next_sibling).to_equal(-1)
```

</details>

### set_attribute

#### stored via get_attribute

1. tree set attribute
   - Expected: got.unwrap() equals `container`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
val elem_id = tree.create_element("div")
tree.set_attribute(elem_id, "class", "container")
val got = tree.get_attribute(elem_id, "class")
expect(got.unwrap()).to_equal("container")
val missing = tree.get_attribute(elem_id, "id")
expect(missing).to_be_nil()
```

</details>

#### replacing same name updates value

1. tree set attribute
2. tree set attribute
   - Expected: got.unwrap() equals `second`
   - Expected: node.attributes.len().to_i64() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
val elem_id = tree.create_element("div")
tree.set_attribute(elem_id, "class", "first")
tree.set_attribute(elem_id, "class", "second")
val got = tree.get_attribute(elem_id, "class")
expect(got.unwrap()).to_equal("second")
val node = tree.get_node(elem_id).unwrap()
expect(node.attributes.len().to_i64()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

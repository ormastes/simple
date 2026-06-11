# Generic Btree Spike Specification

> <details>

<!-- sdn-diagram:id=generic_btree_spike_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generic_btree_spike_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generic_btree_spike_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generic_btree_spike_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Btree Spike Specification

## Scenarios

### Simple generics — TestNode<K> struct

#### can create generic struct with i64 via static new

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = TestNode<i64>.new()
expect(node.count).to_equal(0)
expect(node.keys.len()).to_equal(0)
```

</details>

#### can insert a key into a generic struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = TestNode<i64>.new()
val node2 = node.insert(42)
expect(node2.count).to_equal(1)
expect(node2.keys.len()).to_equal(1)
```

</details>

#### can create generic struct with text key type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = TestNode<text>.new()
val node2 = node.insert("hello")
expect(node2.count).to_equal(1)
```

</details>

### Simple generics — type aliases

#### type alias IntNode forwards static constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = IntNode.new()
expect(node.count).to_equal(0)
```

</details>

#### type alias TextNode forwards static constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = TextNode.new()
expect(node.count).to_equal(0)
```

</details>

#### type alias two-param generic static new has interpreter limitation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Direct construction via concrete type works:
val pair = BTreeNode<i64, text>.new(1, "one")
expect(pair.node_key).to_equal(1)
expect(pair.node_val).to_equal("one")
```

</details>

### Simple generics — two-parameter BTreeNode<K, V>

#### can create BTreeNode<i64, text> directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BTreeNode<i64, text>.new(10, "ten")
expect(node.node_key).to_equal(10)
expect(node.node_val).to_equal("ten")
```

</details>

### Simple generics — where clause SortedNode<K>

#### can create SortedNode<i64> with where clause

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = SortedNode<i64>.new()
expect(node.keys.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/language/generic_btree_spike_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple generics — TestNode<K> struct
- Simple generics — type aliases
- Simple generics — two-parameter BTreeNode<K, V>
- Simple generics — where clause SortedNode<K>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

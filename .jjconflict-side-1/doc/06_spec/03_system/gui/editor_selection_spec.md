# Editor Selection Specification

> <details>

<!-- sdn-diagram:id=editor_selection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_selection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_selection_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_selection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Selection Specification

## Scenarios

### SelectionState — empty

#### empty selection is_empty is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sel = SelectionState.empty()
expect(sel.is_empty()).to_equal(true)
```

</details>

#### empty selection count is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sel = SelectionState.empty()
expect(sel.count()).to_equal(0)
```

</details>

### SelectionState — select

#### select node sets count to 1

1. var sel = SelectionState empty
2. sel select
   - Expected: sel.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sel = SelectionState.empty()
val node = NodeId(id: 1)
sel.select(node)
expect(sel.count()).to_equal(1)
```

</details>

#### select node makes contains return true

1. var sel = SelectionState empty
2. sel select
   - Expected: sel contains `node`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sel = SelectionState.empty()
val node = NodeId(id: 1)
sel.select(node)
expect(sel.contains(node)).to_equal(true)
```

</details>

### SelectionState — add to selection

#### add_to_selection increases count

1. var sel = SelectionState empty
2. sel select
3. sel add to selection
   - Expected: sel.count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sel = SelectionState.empty()
val n1 = NodeId(id: 1)
val n2 = NodeId(id: 2)
sel.select(n1)
sel.add_to_selection(n2)
expect(sel.count()).to_equal(2)
```

</details>

### SelectionState — deselect

#### deselect decreases count

1. var sel = SelectionState empty
2. sel select
3. sel add to selection
4. sel deselect
   - Expected: sel.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sel = SelectionState.empty()
val n1 = NodeId(id: 1)
val n2 = NodeId(id: 2)
sel.select(n1)
sel.add_to_selection(n2)
sel.deselect(n1)
expect(sel.count()).to_equal(1)
```

</details>

#### deselect makes contains return false

1. var sel = SelectionState empty
2. sel select
3. sel deselect
   - Expected: sel does not contain `node`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sel = SelectionState.empty()
val node = NodeId(id: 1)
sel.select(node)
sel.deselect(node)
expect(sel.contains(node)).to_equal(false)
```

</details>

### SelectionState — clear

#### clear makes is_empty true

1. var sel = SelectionState empty
2. sel select
3. sel clear
   - Expected: sel.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sel = SelectionState.empty()
val node = NodeId(id: 1)
sel.select(node)
sel.clear()
expect(sel.is_empty()).to_equal(true)
```

</details>

### SelectionState — primary node

#### primary node tracks first selected

1. var sel = SelectionState empty
2. sel select
   - Expected: sel.primary_node.id equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sel = SelectionState.empty()
val n1 = NodeId(id: 42)
sel.select(n1)
expect(sel.primary_node.id).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_selection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SelectionState — empty
- SelectionState — select
- SelectionState — add to selection
- SelectionState — deselect
- SelectionState — clear
- SelectionState — primary node

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

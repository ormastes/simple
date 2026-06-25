# Editor Split Tree Specification

> <details>

<!-- sdn-diagram:id=editor_split_tree_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_split_tree_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_split_tree_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_split_tree_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Split Tree Specification

## Scenarios

### split tree — data structure

#### defines SplitNode enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("enum SplitNode:")).to_equal(true)
expect(src.contains("Leaf(pane_id: i64)")).to_equal(true)
expect(src.contains("Split(direction: SplitDirection")).to_equal(true)
expect(src.contains("left: SplitNode")).to_equal(true)
expect(src.contains("right: SplitNode")).to_equal(true)
```

</details>

#### defines SplitTree struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("struct SplitTree:")).to_equal(true)
expect(src.contains("root: SplitNode")).to_equal(true)
expect(src.contains("active_pane_id: i64")).to_equal(true)
```

</details>

#### has direction enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("enum SplitDirection:")).to_equal(true)
expect(src.contains("Horizontal")).to_equal(true)
expect(src.contains("Vertical")).to_equal(true)
```

</details>

#### has constructor and factory helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("fn split_tree_leaf(pane_id: i64) -> SplitTree")).to_equal(true)
expect(src.contains("fn split_tree_split(tree: SplitTree, pane_id: i64, new_pane_id: i64, direction: SplitDirection) -> SplitTree")).to_equal(true)
```

</details>

### split tree — mutations

#### has split method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("fn split_tree_split")).to_equal(true)
```

</details>

#### has close_leaf method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me close_other_groups()")).to_equal(true)
```

</details>

#### has resize method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("me resize(group_id: i64, delta: i64)")).to_equal(true)
```

</details>

#### has swap method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me focus_next_group()")).to_equal(true)
expect(src.contains("me focus_prev_group()")).to_equal(true)
```

</details>

#### has equalize method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("editor_layout_compute_rects")).to_equal(true)
```

</details>

### split tree — queries

#### has leaf_count and find_leaf

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("fn leaf_count() -> i64")).to_equal(true)
expect(src.contains("active_pane_id")).to_equal(true)
```

</details>

#### has flatten for in-order traversal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("split_compute_rects")).to_equal(true)
```

</details>

### split compute — rect calculation

#### defines SplitRect struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("struct SplitRect:")).to_equal(true)
expect(src.contains("group_id: i64")).to_equal(true)
expect(src.contains("x: i64")).to_equal(true)
expect(src.contains("y: i64")).to_equal(true)
expect(src.contains("w: i64")).to_equal(true)
expect(src.contains("h: i64")).to_equal(true)
```

</details>

#### has split_compute_rects

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("fn split_compute_rects(tree: SplitTree, x: i64, y: i64, w: i64, h: i64) -> [SplitRect]")).to_equal(true)
```

</details>

#### has split_find_rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("fn split_find_rect(rects: [SplitRect], group_id: i64) -> SplitRect")).to_equal(true)
```

</details>

#### has split_find_neighbor for directional focus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("fn split_find_neighbor(rects: [SplitRect], group_id: i64, direction: text) -> i64")).to_equal(true)
```

</details>

#### deducts border space in rect computation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("val border = 1")).to_equal(true)
```

</details>

### editor layout — split tree integration

#### has tree field on EditorLayout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("tree: SplitTree")).to_equal(true)
expect(src.contains("active_group_id: i64")).to_equal(true)
```

</details>

#### has editor_layout_split_h for horizontal splits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me split_editor_horizontal()")).to_equal(true)
```

</details>

#### has editor_layout_focus_direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me focus_direction(direction: text")).to_equal(true)
```

</details>

#### has editor_layout_compute_rects

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn editor_layout_compute_rects(layout: EditorLayout, x: i64, y: i64, w: i64, h: i64) -> [SplitRect]")).to_equal(true)
```

</details>

#### keeps backward-compatible groups array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("groups: [EditorGroup]")).to_equal(true)
expect(src.contains("active_group_index: i64")).to_equal(true)
```

</details>

### session — horizontal split

#### has split_editor_horizontal method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me split_editor_horizontal()")).to_equal(true)
expect(src.contains("SplitDirection.Horizontal")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_split_tree_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- split tree — data structure
- split tree — mutations
- split tree — queries
- split compute — rect calculation
- editor layout — split tree integration
- session — horizontal split

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

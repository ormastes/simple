# Editor Split Tree Specification

> Tests covering split tree — data structure, split tree — mutations, split tree — queries, split compute — rect calculation, editor layout — split tree integration, session — horizontal split.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Split Tree Specification

## Scenarios

### split tree — data structure

#### defines SplitNode enum

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines SplitNode enum
   - Expected: src contains `enum SplitNode:`
   - Expected: src contains `Leaf(pane_id: i64)`
   - Expected: src contains `Split(direction: SplitDirection`
   - Expected: src contains `left: SplitNode`
   - Expected: src contains `right: SplitNode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SplitNode enum")
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("enum SplitNode:")).to_equal(true)
expect(src.contains("Leaf(pane_id: i64)")).to_equal(true)
expect(src.contains("Split(direction: SplitDirection")).to_equal(true)
expect(src.contains("left: SplitNode")).to_equal(true)
expect(src.contains("right: SplitNode")).to_equal(true)
```

</details>

#### defines SplitTree struct

- defines SplitTree struct
   - Expected: src contains `struct SplitTree:`
   - Expected: src contains `root: SplitNode`
   - Expected: src contains `active_pane_id: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SplitTree struct")
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("struct SplitTree:")).to_equal(true)
expect(src.contains("root: SplitNode")).to_equal(true)
expect(src.contains("active_pane_id: i64")).to_equal(true)
```

</details>

#### has direction enum

- has direction enum
   - Expected: src contains `enum SplitDirection:`
   - Expected: src contains `Horizontal`
   - Expected: src contains `Vertical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has direction enum")
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("enum SplitDirection:")).to_equal(true)
expect(src.contains("Horizontal")).to_equal(true)
expect(src.contains("Vertical")).to_equal(true)
```

</details>

#### has constructor and factory helpers

- has constructor and factory helpers
   - Expected: src contains `fn split_tree_leaf(pane_id: i64) -> SplitTree`
   - Expected: src contains `fn split_tree_split(tree: SplitTree, pane_id: i64, new_pane_id: i64, directio... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has constructor and factory helpers")
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("fn split_tree_leaf(pane_id: i64) -> SplitTree")).to_equal(true)
expect(src.contains("fn split_tree_split(tree: SplitTree, pane_id: i64, new_pane_id: i64, direction: SplitDirection) -> SplitTree")).to_equal(true)
```

</details>

### split tree — mutations

#### has split method

- has split method
   - Expected: src contains `fn split_tree_split`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has split method")
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("fn split_tree_split")).to_equal(true)
```

</details>

#### has close_leaf method

- has close_leaf method
   - Expected: src contains `me close_other_groups()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has close_leaf method")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me close_other_groups()")).to_equal(true)
```

</details>

#### has resize method

- has resize method
   - Expected: src contains `me resize(group_id: i64, delta: i64)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has resize method")
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("me resize(group_id: i64, delta: i64)")).to_equal(true)
```

</details>

#### has swap method

- has swap method
   - Expected: src contains `me focus_next_group()`
   - Expected: src contains `me focus_prev_group()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has swap method")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me focus_next_group()")).to_equal(true)
expect(src.contains("me focus_prev_group()")).to_equal(true)
```

</details>

#### has equalize method

- has equalize method
   - Expected: src contains `editor_layout_compute_rects`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has equalize method")
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("editor_layout_compute_rects")).to_equal(true)
```

</details>

### split tree — queries

#### has leaf_count and find_leaf

- has leaf_count and find_leaf
   - Expected: src contains `fn leaf_count() -> i64`
   - Expected: src contains `active_pane_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has leaf_count and find_leaf")
val src = read_text("src/lib/editor/view/split_tree.spl")
expect(src.contains("fn leaf_count() -> i64")).to_equal(true)
expect(src.contains("active_pane_id")).to_equal(true)
```

</details>

#### has flatten for in-order traversal

- has flatten for in-order traversal
   - Expected: src contains `split_compute_rects`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has flatten for in-order traversal")
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("split_compute_rects")).to_equal(true)
```

</details>

### split compute — rect calculation

#### defines SplitRect struct

- defines SplitRect struct
   - Expected: src contains `struct SplitRect:`
   - Expected: src contains `group_id: i64`
   - Expected: src contains `x: i64`
   - Expected: src contains `y: i64`
   - Expected: src contains `w: i64`
   - Expected: src contains `h: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SplitRect struct")
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

- has split_compute_rects
   - Expected: src contains `fn split_compute_rects(tree: SplitTree, x: i64, y: i64, w: i64, h: i64) -> [S... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has split_compute_rects")
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("fn split_compute_rects(tree: SplitTree, x: i64, y: i64, w: i64, h: i64) -> [SplitRect]")).to_equal(true)
```

</details>

#### has split_find_rect

- has split_find_rect
   - Expected: src contains `fn split_find_rect(rects: [SplitRect], group_id: i64) -> SplitRect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has split_find_rect")
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("fn split_find_rect(rects: [SplitRect], group_id: i64) -> SplitRect")).to_equal(true)
```

</details>

#### has split_find_neighbor for directional focus

- has split_find_neighbor for directional focus
   - Expected: src contains `fn split_find_neighbor(rects: [SplitRect], group_id: i64, direction: text) ->... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has split_find_neighbor for directional focus")
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("fn split_find_neighbor(rects: [SplitRect], group_id: i64, direction: text) -> i64")).to_equal(true)
```

</details>

#### deducts border space in rect computation

- deducts border space in rect computation
   - Expected: src contains `val border = 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deducts border space in rect computation")
val src = read_text("src/lib/editor/view/split_compute.spl")
expect(src.contains("val border = 1")).to_equal(true)
```

</details>

### editor layout — split tree integration

#### has tree field on EditorLayout

- has tree field on EditorLayout
   - Expected: src contains `tree: SplitTree`
   - Expected: src contains `active_group_id: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has tree field on EditorLayout")
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("tree: SplitTree")).to_equal(true)
expect(src.contains("active_group_id: i64")).to_equal(true)
```

</details>

#### has editor_layout_split_h for horizontal splits

- has editor_layout_split_h for horizontal splits
   - Expected: src contains `me split_editor_horizontal()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has editor_layout_split_h for horizontal splits")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me split_editor_horizontal()")).to_equal(true)
```

</details>

#### has editor_layout_focus_direction

- has editor_layout_focus_direction
   - Expected: src contains `me focus_direction(direction: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has editor_layout_focus_direction")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me focus_direction(direction: text")).to_equal(true)
```

</details>

#### has editor_layout_compute_rects

- has editor_layout_compute_rects
   - Expected: src contains `fn editor_layout_compute_rects(layout: EditorLayout, x: i64, y: i64, w: i64, ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has editor_layout_compute_rects")
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn editor_layout_compute_rects(layout: EditorLayout, x: i64, y: i64, w: i64, h: i64) -> [SplitRect]")).to_equal(true)
```

</details>

#### keeps backward-compatible groups array

- keeps backward-compatible groups array
   - Expected: src contains `groups: [EditorGroup]`
   - Expected: src contains `active_group_index: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps backward-compatible groups array")
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("groups: [EditorGroup]")).to_equal(true)
expect(src.contains("active_group_index: i64")).to_equal(true)
```

</details>

### session — horizontal split

#### has split_editor_horizontal method

- has split_editor_horizontal method
   - Expected: src contains `me split_editor_horizontal()`
   - Expected: src contains `SplitDirection.Horizontal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has split_editor_horizontal method")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering split tree — data structure, split tree — mutations, split tree — queries, split compute — rect calculation, editor layout — split tree integration, session — horizontal split.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a9bd3b81e6d9225ae375c302351cc02208bbf5bfe34f9dacfa913ad2a679fa71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9bd3b81e6d9225ae375c302351cc02208bbf5bfe34f9dacfa913ad2a679fa71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9bd3b81e6d9225ae375c302351cc02208bbf5bfe34f9dacfa913ad2a679fa71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_split_tree_spec.spl
mirror: doc/06_spec/03_system/gui/editor_split_tree_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_split_tree_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_split_tree_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_split_tree_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines SplitNode enum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_split_tree_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines SplitTree struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_split_tree_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has direction enum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

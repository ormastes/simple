# Borrow Check Conflict Specification

> <details>

<!-- sdn-diagram:id=borrow_check_conflict_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=borrow_check_conflict_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

borrow_check_conflict_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=borrow_check_conflict_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Borrow Check Conflict Specification

## Scenarios

### WI-4: Place conflict detection functions exist

#### place_conflicts_with function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn place_conflicts_with(a: Place, b: Place) -> bool")).to_equal(true)
```

</details>

#### place_base_equals function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn place_base_equals(a: PlaceBase, b: PlaceBase) -> bool")).to_equal(true)
```

</details>

#### place_elem_equals function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn place_elem_equals(a: PlaceElem, b: PlaceElem) -> bool")).to_equal(true)
```

</details>

### WI-4: Place conflicts logic

#### checks base equality first

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("val same_base = place_base_equals(a.base, b.base)")).to_equal(true)
```

</details>

#### returns false for different bases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("if not same_base")).to_equal(true)
```

</details>

#### checks projection prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("place_elem_equals(a.projections[i], b.projections[i])")).to_equal(true)
```

</details>

### WI-4: Base equals handles all variants

#### handles Local variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Local(a_id)")).to_equal(true)
```

</details>

#### handles Static variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Static(a_name)")).to_equal(true)
```

</details>

#### handles Promoted variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Promoted(a_id)")).to_equal(true)
```

</details>

### WI-4: Elem equals handles all variants

#### handles Deref

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Deref:")).to_equal(true)
```

</details>

#### handles Field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Field(a_idx)")).to_equal(true)
```

</details>

#### handles Index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Index(a_local)")).to_equal(true)
```

</details>

#### handles ConstantIndex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case ConstantIndex(a_idx)")).to_equal(true)
```

</details>

#### handles Downcast

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Downcast(a_v)")).to_equal(true)
```

</details>

### WI-4: Borrow kind conflict detection

#### kind_conflicts_with function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn kind_conflicts_with(a: BorrowKind, b: BorrowKind) -> bool")).to_equal(true)
```

</details>

#### shared+shared returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
# The function should have Shared case returning false for Shared
expect(content.contains("case Shared: false")).to_equal(true)
```

</details>

#### kind_is_mutable function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn kind_is_mutable(kind: BorrowKind) -> bool")).to_equal(true)
```

</details>

### WI-4: Call site fixes

#### borrows_of uses free function place_conflicts_with

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("if place_conflicts_with(borrow.place, place)")).to_equal(true)
```

</details>

#### has_conflicting_borrow uses free function kind_conflicts_with

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("if kind_conflicts_with(borrow.kind, kind)")).to_equal(true)
```

</details>

#### record_assign uses free function kind_is_mutable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("if kind_is_mutable(borrow.kind)")).to_equal(true)
```

</details>

### WI-4: Exports

#### exports conflict detection functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("pub fn place_base_equals")).to_equal(true)
expect(content.contains("pub fn place_elem_equals")).to_equal(true)
expect(content.contains("pub fn place_conflicts_with")).to_equal(true)
expect(content.contains("pub fn kind_conflicts_with")).to_equal(true)
expect(content.contains("pub fn kind_is_mutable")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/borrow_check_conflict_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WI-4: Place conflict detection functions exist
- WI-4: Place conflicts logic
- WI-4: Base equals handles all variants
- WI-4: Elem equals handles all variants
- WI-4: Borrow kind conflict detection
- WI-4: Call site fixes
- WI-4: Exports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

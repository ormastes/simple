# Borrow Check Conflict Specification

> Tests covering WI-4: Place conflict detection functions exist, WI-4: Place conflicts logic, WI-4: Base equals handles all variants, WI-4: Elem equals handles all variants, WI-4: Borrow kind conflict detection, WI-4: Call site fixes, WI-4: Exports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Borrow Check Conflict Specification

## Scenarios

### WI-4: Place conflict detection functions exist

#### place_conflicts_with function defined

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- place_conflicts_with function defined
   - Expected: content contains `fn place_conflicts_with(a: Place, b: Place) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("place_conflicts_with function defined")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn place_conflicts_with(a: Place, b: Place) -> bool")).to_equal(true)
```

</details>

#### place_base_equals function defined

- place_base_equals function defined
   - Expected: content contains `fn place_base_equals(a: PlaceBase, b: PlaceBase) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("place_base_equals function defined")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn place_base_equals(a: PlaceBase, b: PlaceBase) -> bool")).to_equal(true)
```

</details>

#### place_elem_equals function defined

- place_elem_equals function defined
   - Expected: content contains `fn place_elem_equals(a: PlaceElem, b: PlaceElem) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("place_elem_equals function defined")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn place_elem_equals(a: PlaceElem, b: PlaceElem) -> bool")).to_equal(true)
```

</details>

### WI-4: Place conflicts logic

#### checks base equality first

- checks base equality first
   - Expected: content contains `val same_base = place_base_equals(a.base, b.base)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks base equality first")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("val same_base = place_base_equals(a.base, b.base)")).to_equal(true)
```

</details>

#### returns false for different bases

- returns false for different bases
   - Expected: content contains `if not same_base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for different bases")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("if not same_base")).to_equal(true)
```

</details>

#### checks projection prefix

- checks projection prefix
   - Expected: content contains `place_elem_equals(a.projections[i], b.projections[i])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks projection prefix")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("place_elem_equals(a.projections[i], b.projections[i])")).to_equal(true)
```

</details>

### WI-4: Base equals handles all variants

#### handles Local variant

- handles Local variant
   - Expected: content contains `case Local(a_id)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Local variant")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Local(a_id)")).to_equal(true)
```

</details>

#### handles Static variant

- handles Static variant
   - Expected: content contains `case Static(a_name)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Static variant")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Static(a_name)")).to_equal(true)
```

</details>

#### handles Promoted variant

- handles Promoted variant
   - Expected: content contains `case Promoted(a_id)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Promoted variant")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Promoted(a_id)")).to_equal(true)
```

</details>

### WI-4: Elem equals handles all variants

#### handles Deref

- handles Deref
   - Expected: content contains `case Deref:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Deref")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Deref:")).to_equal(true)
```

</details>

#### handles Field

- handles Field
   - Expected: content contains `case Field(a_idx)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Field")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Field(a_idx)")).to_equal(true)
```

</details>

#### handles Index

- handles Index
   - Expected: content contains `case Index(a_local)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Index")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Index(a_local)")).to_equal(true)
```

</details>

#### handles ConstantIndex

- handles ConstantIndex
   - Expected: content contains `case ConstantIndex(a_idx)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles ConstantIndex")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case ConstantIndex(a_idx)")).to_equal(true)
```

</details>

#### handles Downcast

- handles Downcast
   - Expected: content contains `case Downcast(a_v)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Downcast")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("case Downcast(a_v)")).to_equal(true)
```

</details>

### WI-4: Borrow kind conflict detection

#### kind_conflicts_with function defined

- kind_conflicts_with function defined
   - Expected: content contains `fn kind_conflicts_with(a: BorrowKind, b: BorrowKind) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("kind_conflicts_with function defined")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn kind_conflicts_with(a: BorrowKind, b: BorrowKind) -> bool")).to_equal(true)
```

</details>

#### shared+shared returns false

- shared+shared returns false
   - Expected: content contains `case Shared: false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shared+shared returns false")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
# The function should have Shared case returning false for Shared
expect(content.contains("case Shared: false")).to_equal(true)
```

</details>

#### kind_is_mutable function defined

- kind_is_mutable function defined
   - Expected: content contains `fn kind_is_mutable(kind: BorrowKind) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("kind_is_mutable function defined")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("fn kind_is_mutable(kind: BorrowKind) -> bool")).to_equal(true)
```

</details>

### WI-4: Call site fixes

#### borrows_of uses free function place_conflicts_with

- borrows_of uses free function place_conflicts_with
   - Expected: content contains `if place_conflicts_with(borrow.place, place)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("borrows_of uses free function place_conflicts_with")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("if place_conflicts_with(borrow.place, place)")).to_equal(true)
```

</details>

#### has_conflicting_borrow uses free function kind_conflicts_with

- has_conflicting_borrow uses free function kind_conflicts_with
   - Expected: content contains `if kind_conflicts_with(borrow.kind, kind)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_conflicting_borrow uses free function kind_conflicts_with")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("if kind_conflicts_with(borrow.kind, kind)")).to_equal(true)
```

</details>

#### record_assign uses free function kind_is_mutable

- record_assign uses free function kind_is_mutable
   - Expected: content contains `if kind_is_mutable(borrow.kind)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("record_assign uses free function kind_is_mutable")
val content = rt_file_read_text("src/compiler/55.borrow/borrow_check/borrow_graph.spl") ?? ""
expect(content.contains("if kind_is_mutable(borrow.kind)")).to_equal(true)
```

</details>

### WI-4: Exports

#### exports conflict detection functions

- exports conflict detection functions
   - Expected: content contains `pub fn place_base_equals`
   - Expected: content contains `pub fn place_elem_equals`
   - Expected: content contains `pub fn place_conflicts_with`
   - Expected: content contains `pub fn kind_conflicts_with`
   - Expected: content contains `pub fn kind_is_mutable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports conflict detection functions")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WI-4: Place conflict detection functions exist, WI-4: Place conflicts logic, WI-4: Base equals handles all variants, WI-4: Elem equals handles all variants, WI-4: Borrow kind conflict detection, WI-4: Call site fixes, WI-4: Exports.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `840fa6f79b56f858ee3c9734da2f1d5ea8c60fedc3913273830c1130e742f68a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `840fa6f79b56f858ee3c9734da2f1d5ea8c60fedc3913273830c1130e742f68a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `840fa6f79b56f858ee3c9734da2f1d5ea8c60fedc3913273830c1130e742f68a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/borrow_check_conflict_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/borrow_check_conflict_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/borrow_check_conflict_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/borrow_check_conflict_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/borrow_check_conflict_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'place_conflicts_with function defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/borrow_check_conflict_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'place_base_equals function defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/borrow_check_conflict_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'place_elem_equals function defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

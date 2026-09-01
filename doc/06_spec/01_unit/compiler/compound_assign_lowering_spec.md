# HIR lowering: augmented assignment must keep its operator

> `HirStmt::Assign` carries a target and a value but **no operator**. The AST node `Node::Assignment` does carry one (`AssignOp::AddAssign`, `SubAssign`, ...), and the HIR lowering used to drop it on the floor: every augmented assignment was emitted as a plain `target = value`, storing the bare right-hand side.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR lowering: augmented assignment must keep its operator

`HirStmt::Assign` carries a target and a value but **no operator**. The AST node `Node::Assignment` does carry one (`AssignOp::AddAssign`, `SubAssign`, ...), and the HIR lowering used to drop it on the floor: every augmented assignment was emitted as a plain `target = value`, storing the bare right-hand side.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Codegen / HIR lowering parity |
| Status | Active |
| Source | `test/01_unit/compiler/compound_assign_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`HirStmt::Assign` carries a target and a value but **no operator**. The AST node
`Node::Assignment` does carry one (`AssignOp::AddAssign`, `SubAssign`, ...), and
the HIR lowering used to drop it on the floor: every augmented assignment was
emitted as a plain `target = value`, storing the bare right-hand side.

So `p.f += 5` did not compute `p.f + 5` — it stored `5`.

The original bug report called this "loads zero", because for `+=` a discarded
operator and a zeroed load are indistinguishable (`0 + 5` and `5` are both 5).
The other operators separate the two theories and refute the zero-load reading:

| statement          | expected | zeroed load | operator dropped | observed |
|--------------------|----------|-------------|------------------|----------|
| `g = 100; g -= 40` | 60       | -40         | 40               | 40       |
| `g = 40;  g *= 2`  | 80       | 0           | 2                | 2        |

The value stored is always exactly the right-hand side, so the defect is a
*dropped operator*, not a bad load.

This was never struct-specific either. Everything that lowers through
`Node::Assignment` was affected: plain locals, struct fields, class fields, and
index targets. Only the tree-walking interpreter was correct, because it has its
own assignment path that reads `assign.op` — which is precisely why no spec
caught this. `simple test` runs the interpreter, so the assertions below only
become an active gate when exercised on a compiled lane.

An explicit `x = x + v` was always correct, since that is already `AssignOp::Assign`.

## Syntax

```simple
var p = P(10, 100)
p.f += 5      # must be 15, not 5
p.g -= 40     # must be 60, not 40
```

## Scenarios

### augmented assignment keeps its operator through HIR lowering

#### adds to a struct field instead of overwriting it

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### reads the previously written value on a repeated compound assign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(struct_field_add_twice(), 20)
```

</details>

#### subtracts from a struct field (not 40 from a dropped op, not -40 from a zero load)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(struct_field_sub(), 60)
```

</details>

#### multiplies a struct field (not 2 from a dropped op, not 0 from a zero load)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(struct_field_mul(), 80)
```

</details>

#### divides a struct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(struct_field_div(), 30)
```

</details>

#### takes the remainder of a struct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(struct_field_mod(), 7)
```

</details>

#### adds to a class field

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(class_field_add(), 13)
```

</details>

#### adds to a plain local

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(local_add(), 15)
```

</details>

#### subtracts from a plain local

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(local_sub(), 60)
```

</details>

<details>
<summary>Advanced: accumulates across loop iterations</summary>

#### accumulates across loop iterations

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(local_accumulate(), 10)
```

</details>


</details>

#### still evaluates the explicit read-modify-write form correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(explicit_read_modify_write(), 12)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `28d51cbbd06f8e7dcfee731b674106717a62e38345dd8a2e0a5b11312e4e16ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28d51cbbd06f8e7dcfee731b674106717a62e38345dd8a2e0a5b11312e4e16ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28d51cbbd06f8e7dcfee731b674106717a62e38345dd8a2e0a5b11312e4e16ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/compound_assign_lowering_spec.spl
mirror: doc/06_spec/01_unit/compiler/compound_assign_lowering_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/compound_assign_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/compound_assign_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/compound_assign_lowering_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/compound_assign_lowering_spec.spl:134:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'adds to a struct field instead of overwriting it' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/compound_assign_lowering_spec.spl:139:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reads the previously written value on a repeated compound assign' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/compound_assign_lowering_spec.spl:142:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'subtracts from a struct field (not 40 from a dropped op, not -40 from a zero load)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/compound_assign_lowering_spec.spl:145:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'multiplies a struct field (not 2 from a dropped op, not 0 from a zero load)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

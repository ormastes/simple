# Hir Type Structural Equality Specification

> Tests covering HIR structural type equality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Type Structural Equality Specification

## Scenarios

### HIR structural type equality

#### treats equal-but-distinct structures built at different spans as equal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats equal-but-distinct structures built at different spans as equal
   - Expected: hir_types_equal(a, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats equal-but-distinct structures built at different spans as equal")
# Same shape, different HirType values, different spans.
val a = ty(HirTypeKind.Optional(ty(HirTypeKind.Tuple([i32_(), u8_()]))))
val b = ty_at(HirTypeKind.Optional(ty_at(HirTypeKind.Tuple([i32_(), u8_()]), 7)), 9)
expect(hir_types_equal(a, b)).to_equal(true)
```

</details>

#### compares generic named types by symbol and by type arguments

- compares generic named types by symbol and by type arguments
   - Expected: hir_types_equal(vec_i32_a, vec_i32_b) is true
   - Expected: hir_types_equal(vec_i32_a, vec_u8) is false
   - Expected: hir_types_equal(vec_i32_a, other_ctor) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares generic named types by symbol and by type arguments")
val vec_i32_a = ty(HirTypeKind.Named(SymbolId.new(11), [i32_()]))
val vec_i32_b = ty(HirTypeKind.Named(SymbolId.new(11), [i32_()]))
val vec_u8 = ty(HirTypeKind.Named(SymbolId.new(11), [u8_()]))
val other_ctor = ty(HirTypeKind.Named(SymbolId.new(12), [i32_()]))
expect(hir_types_equal(vec_i32_a, vec_i32_b)).to_equal(true)
expect(hir_types_equal(vec_i32_a, vec_u8)).to_equal(false)
expect(hir_types_equal(vec_i32_a, other_ctor)).to_equal(false)
```

</details>

#### compares pointer and reference mutability and pointee

- compares pointer and reference mutability and pointee
   - Expected: hir_types_equal(pa, pb) is true
   - Expected: hir_types_equal(pa, pc) is false
   - Expected: hir_types_equal(pa, ra) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares pointer and reference mutability and pointee")
val pa = ty(HirTypeKind.Ptr(i32_(), true))
val pb = ty(HirTypeKind.Ptr(i32_(), true))
val pc = ty(HirTypeKind.Ptr(i32_(), false))
val ra = ty(HirTypeKind.Ref(i32_(), true))
expect(hir_types_equal(pa, pb)).to_equal(true)
expect(hir_types_equal(pa, pc)).to_equal(false)
expect(hir_types_equal(pa, ra)).to_equal(false)
```

</details>

#### treats the declared array length as part of the type

- treats the declared array length as part of the type
   - Expected: hir_types_equal(a3, a3b) is true
   - Expected: hir_types_equal(a3, a4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats the declared array length as part of the type")
val a3 = ty(HirTypeKind.Array(i32_(), Some(3)))
val a3b = ty(HirTypeKind.Array(i32_(), Some(3)))
val a4 = ty(HirTypeKind.Array(i32_(), Some(4)))
expect(hir_types_equal(a3, a3b)).to_equal(true)
expect(hir_types_equal(a3, a4)).to_equal(false)
```

</details>

#### compares function types by parameters and return type

- compares function types by parameters and return type
   - Expected: hir_types_equal(f1, f2) is true
   - Expected: hir_types_equal(f1, f3) is false
   - Expected: hir_types_equal(f1, f4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares function types by parameters and return type")
val f1 = ty(HirTypeKind.Function([i32_(), u8_()], i32_(), []))
val f2 = ty(HirTypeKind.Function([i32_(), u8_()], i32_(), []))
val f3 = ty(HirTypeKind.Function([i32_()], i32_(), []))
val f4 = ty(HirTypeKind.Function([i32_(), u8_()], u8_(), []))
expect(hir_types_equal(f1, f2)).to_equal(true)
expect(hir_types_equal(f1, f3)).to_equal(false)
expect(hir_types_equal(f1, f4)).to_equal(false)
```

</details>

#### rejects genuinely unequal primitives and constructors

- rejects genuinely unequal primitives and constructors
   - Expected: hir_types_equal(i32_(), u8_()) is false
   - Expected: hir_types_equal(i32_(), ty(HirTypeKind.Str)) is false
   - Expected: hir_types_equal(i32_(), ty(HirTypeKind.Bool)) is false
   - Expected: hir_types_equal(ty(HirTypeKind.Str), ty(HirTypeKind.Bool)) is false
   - Expected: hir_types_equal(ty(HirTypeKind.Unit), ty(HirTypeKind.Unit)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects genuinely unequal primitives and constructors")
expect(hir_types_equal(i32_(), u8_())).to_equal(false)
expect(hir_types_equal(i32_(), ty(HirTypeKind.Str))).to_equal(false)
expect(hir_types_equal(i32_(), ty(HirTypeKind.Bool))).to_equal(false)
expect(hir_types_equal(ty(HirTypeKind.Str), ty(HirTypeKind.Bool))).to_equal(false)
expect(hir_types_equal(ty(HirTypeKind.Unit), ty(HirTypeKind.Unit))).to_equal(true)
```

</details>

#### terminates on a self-referential named type and compares it structurally

- terminates on a self-referential named type and compares it structurally
   - Expected: hir_types_equal(next_a, next_b) is true
   - Expected: hir_types_equal(next_a, other) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("terminates on a self-referential named type and compares it structurally")
# `class Node: next: Node?` -- the recursive occurrence is a Named
# symbol reference, never expanded, so equality is a finite descent.
val node = SymbolId.new(42)
val node_ref_a = ty(HirTypeKind.Named(node, []))
val next_a = ty(HirTypeKind.Optional(ty(HirTypeKind.Named(node, [node_ref_a]))))
val node_ref_b = ty(HirTypeKind.Named(node, []))
val next_b = ty(HirTypeKind.Optional(ty(HirTypeKind.Named(node, [node_ref_b]))))
expect(hir_types_equal(next_a, next_b)).to_equal(true)

val other = ty(HirTypeKind.Optional(ty(HirTypeKind.Named(node, [i32_()]))))
expect(hir_types_equal(next_a, other)).to_equal(false)
```

</details>

#### compares union and dyn-trait types structurally

- compares union and dyn-trait types structurally
   - Expected: hir_types_equal(u1, u2) is true
   - Expected: hir_types_equal(u1, u3) is false
   - Expected: hir_types_equal(d1, d2) is true
   - Expected: hir_types_equal(d1, d3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares union and dyn-trait types structurally")
val u1 = ty(HirTypeKind.Union([i32_(), u8_()]))
val u2 = ty(HirTypeKind.Union([i32_(), u8_()]))
val u3 = ty(HirTypeKind.Union([i32_()]))
expect(hir_types_equal(u1, u2)).to_equal(true)
expect(hir_types_equal(u1, u3)).to_equal(false)

val d1 = ty(HirTypeKind.DynTrait(SymbolId.new(5)))
val d2 = ty(HirTypeKind.DynTrait(SymbolId.new(5)))
val d3 = ty(HirTypeKind.DynTrait(SymbolId.new(6)))
expect(hir_types_equal(d1, d2)).to_equal(true)
expect(hir_types_equal(d1, d3)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_type_structural_equality_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR structural type equality.
- HIR structural type equality

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `73f4906064d7a3e7ca1ab4d1b30173e7479bf4cd28ea38aab4ee77c27d41ca32`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73f4906064d7a3e7ca1ab4d1b30173e7479bf4cd28ea38aab4ee77c27d41ca32`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73f4906064d7a3e7ca1ab4d1b30173e7479bf4cd28ea38aab4ee77c27d41ca32`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/hir_type_structural_equality_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_type_structural_equality_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_type_structural_equality_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_type_structural_equality_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_type_structural_equality_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats equal-but-distinct structures built at different spans as equal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_type_structural_equality_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares generic named types by symbol and by type arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_type_structural_equality_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares pointer and reference mutability and pointee' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

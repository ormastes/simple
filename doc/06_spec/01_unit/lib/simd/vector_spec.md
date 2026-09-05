# Vector Trait Unit Tests — Trait Surface (D5 kickoff)

> Unit tests for the `Vector` trait abstraction: generic functions bounded by `Vector`, lane count query, and splat through concrete implementations. Corresponds to D5 trait-surface kickoff test IDs V-01 through V-03.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Trait Unit Tests — Trait Surface (D5 kickoff)

Unit tests for the `Vector` trait abstraction: generic functions bounded by `Vector`, lane count query, and splat through concrete implementations. Corresponds to D5 trait-surface kickoff test IDs V-01 through V-03.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-VECTOR |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Design | doc/04_architecture/simd_unified_architecture_detail.md §1.1 |
| Source | `test/01_unit/lib/simd/vector_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for the `Vector` trait abstraction: generic functions bounded by
`Vector`, lane count query, and splat through concrete implementations.
Corresponds to D5 trait-surface kickoff test IDs V-01 through V-03.

Uses back-compat aliases (C2 §11.3): Vec4f = FixedVec<f32,4>,
Vec4i = FixedVec<i32,4>, Vec8i = FixedVec<i32,8> — avoids parser limitation
with integer const-generic arguments in type-expression position.

Per C2 §1.1: `Vector` has NO constructors — splat lives on the concrete type.
V-03 calls `Vec4i.splat(7)` (not a hypothetical `Vector.splat`).

All tests run in interpreter mode. Expected result before D4 lands:
0 passing (import resolution fails). After D4 lands: 3/3 passing.

## Scenarios

### Vector trait abstraction

#### V-01: generic add via Vector trait doubles each lane for f32x4 and i32x8

- V-01: generic add via Vector trait doubles each lane for f32x4 and i32x8
   - Expected: arr_f[0] equals `2.0`
   - Expected: arr_f[1] equals `4.0`
   - Expected: arr_f[2] equals `6.0`
   - Expected: arr_f[3] equals `8.0`
   - Expected: arr_i[0] equals `2`
   - Expected: arr_i[7] equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("V-01: generic add via Vector trait doubles each lane for f32x4 and i32x8")
# f32x4: [1,2,3,4] doubled = [2,4,6,8]
val vf = Vec4f.from_array([1.0, 2.0, 3.0, 4.0])
val doubled_f = double_f32x4(vf)
val arr_f = doubled_f.to_array()
expect(arr_f[0]).to_equal(2.0)
expect(arr_f[1]).to_equal(4.0)
expect(arr_f[2]).to_equal(6.0)
expect(arr_f[3]).to_equal(8.0)

# i32x8: [1,2,3,4,5,6,7,8] doubled = [2,4,6,8,10,12,14,16]
val vi = Vec8i.from_array([1, 2, 3, 4, 5, 6, 7, 8])
val doubled_i = double_i32x8(vi)
val arr_i = doubled_i.to_array()
expect(arr_i[0]).to_equal(2)
expect(arr_i[7]).to_equal(16)
```

</details>

#### V-02: lanes() via Vector trait returns N for FixedVec

- V-02: lanes() via Vector trait returns N for FixedVec
   - Expected: cf equals `4`
   - Expected: ci equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("V-02: lanes() via Vector trait returns N for FixedVec")
val vf = Vec4f.splat(0.0)
val cf = lane_count_f32x4(vf)
expect(cf).to_equal(4)

val vi = Vec8i.splat(0)
val ci = lane_count_i32x8(vi)
expect(ci).to_equal(8)
```

</details>

#### V-03: Vec4i.splat(7) produces four lanes of 7

- V-03: Vec4i.splat(7) produces four lanes of 7
   - Expected: arr[0] equals `7`
   - Expected: arr[1] equals `7`
   - Expected: arr[2] equals `7`
   - Expected: arr[3] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("V-03: Vec4i.splat(7) produces four lanes of 7")
val v = Vec4i.splat(7)
val arr = v.to_array()
expect(arr[0]).to_equal(7)
expect(arr[1]).to_equal(7)
expect(arr[2]).to_equal(7)
expect(arr[3]).to_equal(7)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/04_architecture/simd_unified_architecture_detail.md §1.1`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a88c20b3222970ec52aec719228b4b1a06bbd34ae531c7618355869db23d9755`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a88c20b3222970ec52aec719228b4b1a06bbd34ae531c7618355869db23d9755`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a88c20b3222970ec52aec719228b4b1a06bbd34ae531c7618355869db23d9755`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/simd/vector_spec.spl
mirror: doc/06_spec/01_unit/lib/simd/vector_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/simd/vector_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/simd/vector_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/simd/vector_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/simd/vector_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V-01: generic add via Vector trait doubles each lane for f32x4 and i32x8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/simd/vector_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V-02: lanes() via Vector trait returns N for FixedVec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/simd/vector_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V-03: Vec4i.splat(7) produces four lanes of 7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

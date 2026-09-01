# Simd Check Specification

> Tests covering SimdElementType lanes, SimdElementType elementwise ops, SimdElementType reductions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Check Specification

## Scenarios

### SimdElementType lanes

#### accepts a power-of-two lane count

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- build a 4-lane i32 vector and read its lane count
   - Expected: v.len() equals `4`
   - Expected: v.lane(0) equals `1`
   - Expected: v.lane(3) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("build a 4-lane i32 vector and read its lane count")
val v = FixedVec<i32>.from_array([1, 2, 3, 4])
# oracle: from_array preserves the declared lane count
expect(v.len()).to_equal(4)
expect(v.lane(0)).to_equal(1)
expect(v.lane(3)).to_equal(4)
```

</details>

#### supports lane mutation through set_lane

- overwrite lane 2 and read it back
   - Expected: v.lane(2) equals `99`
   - Expected: v.lane(1) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("overwrite lane 2 and read it back")
val v = FixedVec<i32>.from_array([1, 2, 3, 4]).set_lane(2, 99)
# oracle: only the addressed lane changes
expect(v.lane(2)).to_equal(99)
expect(v.lane(1)).to_equal(2)
```

</details>

### SimdElementType elementwise ops

#### add, sub and mul operate per lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- elementwise arithmetic over two 4-lane vectors
   - Expected: a.add(b).to_array() equals `[11, 22, 33, 44]`
   - Expected: a.sub(b).to_array() equals `[-9, -18, -27, -36]`
   - Expected: a.mul(b).to_array() equals `[10, 40, 90, 160]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("elementwise arithmetic over two 4-lane vectors")
val a = FixedVec<i32>.from_array([1, 2, 3, 4])
val b = FixedVec<i32>.from_array([10, 20, 30, 40])
# oracle: lane-wise sums 11,22,33,44; differences -9,-18,-27,-36
expect(a.add(b).to_array()).to_equal([11, 22, 33, 44])
expect(a.sub(b).to_array()).to_equal([-9, -18, -27, -36])
# oracle: lane-wise products 10,40,90,160
expect(a.mul(b).to_array()).to_equal([10, 40, 90, 160])
```

</details>

#### min and max pick per lane

- per-lane min/max between two vectors
   - Expected: a.min(b).to_array() equals `[1, 2, 3, 2]`
   - Expected: a.max(b).to_array() equals `[30, 50, 30, 40]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("per-lane min/max between two vectors")
val a = FixedVec<i32>.from_array([1, 50, 3, 40])
val b = FixedVec<i32>.from_array([30, 2, 30, 2])
# oracle: min picks the smaller lane value at each position
expect(a.min(b).to_array()).to_equal([1, 2, 3, 2])
expect(a.max(b).to_array()).to_equal([30, 50, 30, 40])
```

</details>

### SimdElementType reductions

#### reduce_sum folds all lanes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sum the lanes of a 4-lane vector
   - Expected: v.reduce_sum() equals `10`
   - Expected: v.reduce_min() equals `1`
   - Expected: v.reduce_max() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("sum the lanes of a 4-lane vector")
val v = FixedVec<i32>.from_array([1, 2, 3, 4])
# oracle: 1+2+3+4 = 10
expect(v.reduce_sum()).to_equal(10)
# oracle: lanes 1..4, min 1 max 4
expect(v.reduce_min()).to_equal(1)
expect(v.reduce_max()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/native/simd_check_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimdElementType lanes, SimdElementType elementwise ops, SimdElementType reductions.
- SimdElementType lanes
- SimdElementType elementwise ops
- SimdElementType reductions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `55f52acd5576a361721a92dd254cab4d8cd20ad05520dc15310b2b7c98a0daa9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55f52acd5576a361721a92dd254cab4d8cd20ad05520dc15310b2b7c98a0daa9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55f52acd5576a361721a92dd254cab4d8cd20ad05520dc15310b2b7c98a0daa9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/unit/compiler/native/simd_check_spec.spl
mirror: doc/06_spec/unit/compiler/native/simd_check_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/native/simd_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/native/simd_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/native/simd_check_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/compiler/native/simd_check_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/native/simd_check_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a power-of-two lane count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/native/simd_check_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports lane mutation through set_lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/native/simd_check_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add, sub and mul operate per lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

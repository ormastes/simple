# Fixed/Scalable SIMD Parity + Adapter Tests

> Purpose: Verify FixedVec / ScalableVec arithmetic parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed/Scalable SIMD Parity + Adapter Tests

Purpose: Verify FixedVec / ScalableVec arithmetic parity.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-SCALABLE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Active |
| Design | doc/05_design/simd_fixed_and_scalable_vectors.md |
| Source | `test/01_unit/lib/simd/simd_fixed_scalable_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify FixedVec / ScalableVec arithmetic parity.
Audience: compiler and tooling engineers who maintain this spec.

# Fixed/Scalable SIMD Parity + Adapter Tests

**Feature IDs:** #SIMD-SCALABLE
**Category:** Stdlib
**Difficulty:** 3/5
**Status:** Active
**Design:** doc/05_design/simd_fixed_and_scalable_vectors.md

## Overview

Asserts that FixedVec<T> and ScalableVec<T> produce numerically equivalent
results for shared operations when given identical inputs (parity).

Also covers the ScalableAdapter lowering-diagnostics surface
(scalable_lower_f32, diag_is_ok, diag_is_split, diag_is_pad, diag_note)
using the real library — no inline redefinitions.

## Scenarios

### FixedVec / ScalableVec arithmetic parity

#### P-01: add produces same lane values for f32

- Verify: P-01: add produces same lane values for f32
   - Expected: fixed_add[0] equals `scalable_add[0]`
   - Expected: fixed_add[1] equals `scalable_add[1]`
   - Expected: fixed_add[2] equals `scalable_add[2]`
   - Expected: fixed_add[3] equals `scalable_add[3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: P-01: add produces same lane values for f32")
# @req: REQ-LIB-SIMD-FIXED-SCALABLE-001
val fa = make_fixed_f32()
val fb = make_fixed_f32_rhs()
val sa = make_scalable_f32()
val sb = make_scalable_f32_rhs()

val fixed_add = fa.add(fb).to_array()
val scalable_add = sa.add(sb).to_array()

expect(fixed_add[0]).to_equal(scalable_add[0])
expect(fixed_add[1]).to_equal(scalable_add[1])
expect(fixed_add[2]).to_equal(scalable_add[2])
expect(fixed_add[3]).to_equal(scalable_add[3])
```

</details>

#### P-02: sub produces same lane values for f32

- Verify: P-02: sub produces same lane values for f32
   - Expected: fixed_sub[0] equals `scalable_sub[0]`
   - Expected: fixed_sub[3] equals `scalable_sub[3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: P-02: sub produces same lane values for f32")
val fa = make_fixed_f32()
val fb = make_fixed_f32_rhs()
val sa = make_scalable_f32()
val sb = make_scalable_f32_rhs()

val fixed_sub = fa.sub(fb).to_array()
val scalable_sub = sa.sub(sb).to_array()

expect(fixed_sub[0]).to_equal(scalable_sub[0])
expect(fixed_sub[3]).to_equal(scalable_sub[3])
```

</details>

#### P-03: mul produces same lane values for f32

- Verify: P-03: mul produces same lane values for f32
   - Expected: fixed_mul[0] equals `scalable_mul[0]`
   - Expected: fixed_mul[3] equals `scalable_mul[3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: P-03: mul produces same lane values for f32")
val fa = make_fixed_f32()
val fb = make_fixed_f32_rhs()
val sa = make_scalable_f32()
val sb = make_scalable_f32_rhs()

val fixed_mul = fa.mul(fb).to_array()
val scalable_mul = sa.mul(sb).to_array()

expect(fixed_mul[0]).to_equal(scalable_mul[0])
expect(fixed_mul[3]).to_equal(scalable_mul[3])
```

</details>

#### P-04: reduce_sum returns same total for i32

- Verify: P-04: reduce_sum returns same total for i32
   - Expected: fi.reduce_sum() equals `si.reduce_sum()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: P-04: reduce_sum returns same total for i32")
val fi = make_fixed_i32()
val si = make_scalable_i32()
expect(fi.reduce_sum()).to_equal(si.reduce_sum())
```

</details>

#### P-05: reduce_min and reduce_max agree for i32

- Verify: P-05: reduce_min and reduce_max agree for i32
   - Expected: fi.reduce_min() equals `si.reduce_min()`
   - Expected: fi.reduce_max() equals `si.reduce_max()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: P-05: reduce_min and reduce_max agree for i32")
val fi = make_fixed_i32()
val si = make_scalable_i32()
expect(fi.reduce_min()).to_equal(si.reduce_min())
expect(fi.reduce_max()).to_equal(si.reduce_max())
```

</details>

#### P-06: splat parity — same value in every lane

- Verify: P-06: splat parity — same value in every lane
   - Expected: fv.lane(0) equals `sv.lane(0)`
   - Expected: fv.lane(3) equals `sv.lane(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: P-06: splat parity — same value in every lane")
val fv = fixedvec_splat(7.0, 4)
val sv = scalablevec_splat(7.0)
expect(fv.lane(0)).to_equal(sv.lane(0))
expect(fv.lane(3)).to_equal(sv.lane(3))
```

</details>

#### P-07: from_fixed round-trip preserves all lanes

- Verify: P-07: from_fixed round-trip preserves all lanes
   - Expected: sv.lane(0) equals `fv.lane(0)`
   - Expected: sv.lane(1) equals `fv.lane(1)`
   - Expected: sv.lane(2) equals `fv.lane(2)`
   - Expected: sv.lane(3) equals `fv.lane(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: P-07: from_fixed round-trip preserves all lanes")
val fv = make_fixed_f32()
val sv = scalablevec_from_fixed(fv)
expect(sv.lane(0)).to_equal(fv.lane(0))
expect(sv.lane(1)).to_equal(fv.lane(1))
expect(sv.lane(2)).to_equal(fv.lane(2))
expect(sv.lane(3)).to_equal(fv.lane(3))
```

</details>

### ScalableAdapter lowering diagnostics

#### A-01: direct map when fixed lanes equal target

- Verify: A-01: direct map when fixed lanes equal target
   - Expected: diag_is_ok(d) is true
   - Expected: diag_note(d) equals `direct map`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: A-01: direct map when fixed lanes equal target")
val d = scalable_lower_f32(4, 4)
expect(diag_is_ok(d)).to_equal(true)
expect(diag_note(d)).to_equal("direct map")
```

</details>

#### A-02: split required when fixed lanes exceed target

- Verify: A-02: split required when fixed lanes exceed target
   - Expected: diag_is_split(d) is true
   - Expected: diag_note(d) equals `split required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: A-02: split required when fixed lanes exceed target")
val d = scalable_lower_f32(8, 4)
expect(diag_is_split(d)).to_equal(true)
expect(diag_note(d)).to_equal("split required")
```

</details>

#### A-03: padding required when fixed lanes less than target

- Verify: A-03: padding required when fixed lanes less than target
   - Expected: diag_is_pad(d) is true
   - Expected: diag_note(d) equals `padding required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: A-03: padding required when fixed lanes less than target")
val d = scalable_lower_f32(4, 8)
expect(diag_is_pad(d)).to_equal(true)
expect(diag_note(d)).to_equal("padding required")
```

</details>

#### A-04: kind constants are distinct

- Verify: A-04: kind constants are distinct
   - Expected: lowering_ok() equals `0`
   - Expected: lowering_split() equals `1`
   - Expected: lowering_pad() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: A-04: kind constants are distinct")
expect(lowering_ok()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(lowering_split()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
expect(lowering_pad()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### A-05: fixed_lanes and target_lanes fields are preserved

- Verify: A-05: fixed_lanes and target_lanes fields are preserved
   - Expected: d.fixed_lanes equals `8`
   - Expected: d.target_lanes equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: A-05: fixed_lanes and target_lanes fields are preserved")
val d = scalable_lower_f32(8, 4)
expect(d.fixed_lanes).to_equal(8)  # oracle: authoritative expected value documented by this spec's contract
expect(d.target_lanes).to_equal(4)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/05_design/simd_fixed_and_scalable_vectors.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-LIB-SIMD-FIXED-SCALABLE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `43d3b8e9e7ef375797fa43f2e927932d38e02bf1999821336af55535d37512e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43d3b8e9e7ef375797fa43f2e927932d38e02bf1999821336af55535d37512e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43d3b8e9e7ef375797fa43f2e927932d38e02bf1999821336af55535d37512e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/simd/simd_fixed_scalable_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/simd/simd_fixed_scalable_parity_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/simd/simd_fixed_scalable_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/simd/simd_fixed_scalable_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/simd/simd_fixed_scalable_parity_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/simd/simd_fixed_scalable_parity_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/lib/simd/simd_fixed_scalable_parity_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'P-01: add produces same lane values for f32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/simd/simd_fixed_scalable_parity_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'P-02: sub produces same lane values for f32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/simd/simd_fixed_scalable_parity_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'P-03: mul produces same lane values for f32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

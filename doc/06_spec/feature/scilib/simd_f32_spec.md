# SIMD f32 Intrinsics Specification

> Purpose: Verify SIMD f32x4 arithmetic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SIMD f32 Intrinsics Specification

Purpose: Verify SIMD f32x4 arithmetic.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-C-001, REQ-SCILIB-C-004, NFR-SCILIB-C-001, NFR-SCILIB-C-002 |
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/simd_f32_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify SIMD f32x4 arithmetic.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### SIMD f32x4 arithmetic

#### computes lane-wise add/sub/mul/div

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes lane-wise add/sub/mul/div
- computes lane-wise add/sub/mul/div
   - Expected: added.x equals `10.0`
   - Expected: added.w equals `18.0`
   - Expected: subbed.y equals `6.0`
   - Expected: multiplied.z equals `50.0`
   - Expected: divided.x equals `4.0`
   - Expected: divided.w equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes lane-wise add/sub/mul/div")
step("computes lane-wise add/sub/mul/div")
# @req: REQ-SCILIB-C-001
# @req: REQ-SCILIB-C-004
val a = Vec4f(x: 8.0, y: 9.0, z: 10.0, w: 12.0)
val b = Vec4f(x: 2.0, y: 3.0, z: 5.0, w: 6.0)
val added = simd_add_f32x4(a, b)
val subbed = simd_sub_f32x4(a, b)
val multiplied = simd_mul_f32x4(a, b)
val divided = simd_div_f32x4(a, b)
expect(added.x).to_equal(10.0)
expect(added.w).to_equal(18.0)
expect(subbed.y).to_equal(6.0)
expect(multiplied.z).to_equal(50.0)
expect(divided.x).to_equal(4.0)
expect(divided.w).to_equal(2.0)
```

</details>

#### computes lane-wise fma

- computes lane-wise fma
- computes lane-wise fma
   - Expected: result.x equals `11.0`
   - Expected: result.y equals `20.0`
   - Expected: result.z equals `29.0`
   - Expected: result.w equals `42.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes lane-wise fma")
step("computes lane-wise fma")
val a = Vec4f(x: 1.0, y: 2.0, z: 3.0, w: 4.0)
val b = Vec4f(x: 10.0, y: 10.0, z: 10.0, w: 10.0)
val c = Vec4f(x: 1.0, y: 0.0, z: -1.0, w: 2.0)
val result = simd_fma_f32x4(a, b, c)
expect(result.x).to_equal(11.0)
expect(result.y).to_equal(20.0)
expect(result.z).to_equal(29.0)
expect(result.w).to_equal(42.0)
```

</details>

### SIMD f32x8 arithmetic

#### computes lane-wise add/sub/mul/div across eight lanes

- computes lane-wise add/sub/mul/div across eight lanes
- computes lane-wise add/sub/mul/div across eight lanes
   - Expected: added.e0 equals `10.0`
   - Expected: added.e7 equals `21.0`
   - Expected: subbed.e1 equals `6.0`
   - Expected: multiplied.e2 equals `50.0`
   - Expected: divided.e0 equals `4.0`
   - Expected: divided.e7 equals `6.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes lane-wise add/sub/mul/div across eight lanes")
step("computes lane-wise add/sub/mul/div across eight lanes")
val a = Vec8f(e0: 8.0, e1: 9.0, e2: 10.0, e3: 12.0, e4: 14.0, e5: 15.0, e6: 16.0, e7: 18.0)
val b = Vec8f(e0: 2.0, e1: 3.0, e2: 5.0, e3: 6.0, e4: 7.0, e5: 5.0, e6: 4.0, e7: 3.0)
val added = simd_add_f32x8(a, b)
val subbed = simd_sub_f32x8(a, b)
val multiplied = simd_mul_f32x8(a, b)
val divided = simd_div_f32x8(a, b)
expect(added.e0).to_equal(10.0)
expect(added.e7).to_equal(21.0)
expect(subbed.e1).to_equal(6.0)
expect(multiplied.e2).to_equal(50.0)
expect(divided.e0).to_equal(4.0)
expect(divided.e7).to_equal(6.0)
```

</details>

#### computes lane-wise fma across eight lanes

- computes lane-wise fma across eight lanes
- computes lane-wise fma across eight lanes
   - Expected: fused.e0 equals `9.0`
   - Expected: fused.e3 equals `21.0`
   - Expected: fused.e7 equals `9.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes lane-wise fma across eight lanes")
step("computes lane-wise fma across eight lanes")
val a = Vec8f(e0: 1.0, e1: 2.0, e2: 3.0, e3: 4.0, e4: 5.0, e5: 6.0, e6: 7.0, e7: 8.0)
val b = Vec8f(e0: 8.0, e1: 7.0, e2: 6.0, e3: 5.0, e4: 4.0, e5: 3.0, e6: 2.0, e7: 1.0)
val c = Vec8f.splat(1.0f32)
val fused = simd_fma_f32x8(a, b, c)
expect(fused.e0).to_equal(9.0)
expect(fused.e3).to_equal(21.0)
expect(fused.e7).to_equal(9.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-SCILIB-C-001`
- `REQ-SCILIB-C-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e0d046c9363befe43b7596833099a15cb456804b9a0e6d062ce50056a6b1be8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e0d046c9363befe43b7596833099a15cb456804b9a0e6d062ce50056a6b1be8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e0d046c9363befe43b7596833099a15cb456804b9a0e6d062ce50056a6b1be8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/simd_f32_spec.spl
mirror: doc/06_spec/feature/scilib/simd_f32_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/simd_f32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/simd_f32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/simd_f32_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/simd_f32_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes lane-wise add/sub/mul/div' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/simd_f32_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes lane-wise fma' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/simd_f32_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes lane-wise add/sub/mul/div across eight lanes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

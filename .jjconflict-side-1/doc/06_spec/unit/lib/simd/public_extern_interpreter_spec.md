# Public Extern Interpreter Specification

> Tests covering public SIMD externs in interpreter mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Public Extern Interpreter Specification

## Scenarios

### public SIMD externs in interpreter mode

#### executes u32x4 arithmetic and bitwise externs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes u32x4 arithmetic and bitwise externs
   - Expected: add[0] equals `11u32`
   - Expected: add[1] equals `7u32`
   - Expected: sub[0] equals `9u32`
   - Expected: sub[1] equals `3u32`
   - Expected: anded[2] equals `0x00F0u32`
   - Expected: ored[2] equals `0xFFF0u32`
   - Expected: xored[3] equals `0xFF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes u32x4 arithmetic and bitwise externs")
val a = Vec4u32(x: 1u32, y: 2u32, z: 0xF0F0u32, w: 0xFFFFu32)
val b = Vec4u32(x: 10u32, y: 5u32, z: 0x0FF0u32, w: 0x00FFu32)

val add = simd_add_u32x4(a, b).to_array()
expect(add[0]).to_equal(11u32)
expect(add[1]).to_equal(7u32)

val sub = simd_sub_u32x4(b, a).to_array()
expect(sub[0]).to_equal(9u32)
expect(sub[1]).to_equal(3u32)

val anded = simd_and_u32x4(a, b).to_array()
expect(anded[2]).to_equal(0x00F0u32)

val ored = simd_or_u32x4(a, b).to_array()
expect(ored[2]).to_equal(0xFFF0u32)

val xored = simd_xor_u32x4(a, b).to_array()
expect(xored[3]).to_equal(0xFF00u32)
```

</details>

#### executes i64x4 arithmetic externs

- executes i64x4 arithmetic externs
   - Expected: add[0] equals `11`
   - Expected: add[1] equals `-18`
   - Expected: add[2] equals `27`
   - Expected: add[3] equals `-44`
   - Expected: sub[0] equals `9`
   - Expected: sub[1] equals `-22`
   - Expected: sub[2] equals `33`
   - Expected: sub[3] equals `-36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes i64x4 arithmetic externs")
val a = Vec4i64(x: 10, y: -20, z: 30, w: -40)
val b = Vec4i64(x: 1, y: 2, z: -3, w: -4)

val add = simd_add_i64x4(a, b).to_array()
expect(add[0]).to_equal(11)
expect(add[1]).to_equal(-18)
expect(add[2]).to_equal(27)
expect(add[3]).to_equal(-44)

val sub = simd_sub_i64x4(a, b).to_array()
expect(sub[0]).to_equal(9)
expect(sub[1]).to_equal(-22)
expect(sub[2]).to_equal(33)
expect(sub[3]).to_equal(-36)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/simd/public_extern_interpreter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering public SIMD externs in interpreter mode.
- public SIMD externs in interpreter mode

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `8c1f6e066ef0496da21efc5952a1c8e47ad232c60f4406842714430e4e7af9b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c1f6e066ef0496da21efc5952a1c8e47ad232c60f4406842714430e4e7af9b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c1f6e066ef0496da21efc5952a1c8e47ad232c60f4406842714430e4e7af9b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/simd/public_extern_interpreter_spec.spl
mirror: doc/06_spec/unit/lib/simd/public_extern_interpreter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/simd/public_extern_interpreter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/simd/public_extern_interpreter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/simd/public_extern_interpreter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/simd/public_extern_interpreter_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes u32x4 arithmetic and bitwise externs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/simd/public_extern_interpreter_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes i64x4 arithmetic externs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

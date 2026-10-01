# rotl_rotr_i32x4_spec

> Rotate-left wrapper over simd_shl_i32x4, simd_shr_i32x4, simd_or_i32x4.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rotl_rotr_i32x4_spec

Rotate-left wrapper over simd_shl_i32x4, simd_shr_i32x4, simd_or_i32x4.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/simd/rotl_rotr_i32x4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Rotate-left wrapper over simd_shl_i32x4, simd_shr_i32x4, simd_or_i32x4.
    Test vectors derived from RFC 7539 rotation amounts and hand-computed values.

## Scenarios

### simd_rotl_i32x4

#### rotl by 0 is identity

- rotl by 0 is identity
   - Expected: r.x equals `0x12345678`
   - Expected: r.y equals `0x12345678`
   - Expected: r.z equals `0x12345678`
   - Expected: r.w equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotl by 0 is identity")
val r = simd_rotl_i32x4(_input_12345678(), 0)
expect(r.x).to_equal(0x12345678)
expect(r.y).to_equal(0x12345678)
expect(r.z).to_equal(0x12345678)
expect(r.w).to_equal(0x12345678)
```

</details>

#### rotl by 8: 0x12345678 -> 0x34567812

- rotl by 8: 0x12345678 -> 0x34567812
   - Expected: r.x equals `0x34567812`
   - Expected: r.y equals `0x34567812`
   - Expected: r.z equals `0x34567812`
   - Expected: r.w equals `0x34567812`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotl by 8: 0x12345678 -> 0x34567812")
val r = simd_rotl_i32x4(_input_12345678(), 8)
expect(r.x).to_equal(0x34567812)
expect(r.y).to_equal(0x34567812)
expect(r.z).to_equal(0x34567812)
expect(r.w).to_equal(0x34567812)
```

</details>

#### rotl by 16: 0x12345678 -> 0x56781234

- rotl by 16: 0x12345678 -> 0x56781234
   - Expected: r.x equals `0x56781234`
   - Expected: r.y equals `0x56781234`
   - Expected: r.z equals `0x56781234`
   - Expected: r.w equals `0x56781234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotl by 16: 0x12345678 -> 0x56781234")
val r = simd_rotl_i32x4(_input_12345678(), 16)
expect(r.x).to_equal(0x56781234)
expect(r.y).to_equal(0x56781234)
expect(r.z).to_equal(0x56781234)
expect(r.w).to_equal(0x56781234)
```

</details>

#### rotl by 31: 0x12345678 -> 0x091a2b3c

- rotl by 31: 0x12345678 -> 0x091a2b3c
   - Expected: r.x equals `0x091a2b3c`
   - Expected: r.y equals `0x091a2b3c`
   - Expected: r.z equals `0x091a2b3c`
   - Expected: r.w equals `0x091a2b3c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotl by 31: 0x12345678 -> 0x091a2b3c")
# 0x12345678 << 31 = 0 (bit 0 of 0x78 = 0), >> 1 = 0x091A2B3C
val r = simd_rotl_i32x4(_input_12345678(), 31)
expect(r.x).to_equal(0x091a2b3c)
expect(r.y).to_equal(0x091a2b3c)
expect(r.z).to_equal(0x091a2b3c)
expect(r.w).to_equal(0x091a2b3c)
```

</details>

#### rotl by 32 is identity (n masked to 0)

- rotl by 32 is identity (n masked to 0)
   - Expected: r.x equals `0x12345678`
   - Expected: r.y equals `0x12345678`
   - Expected: r.z equals `0x12345678`
   - Expected: r.w equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotl by 32 is identity (n masked to 0)")
val r = simd_rotl_i32x4(_input_12345678(), 32)
expect(r.x).to_equal(0x12345678)
expect(r.y).to_equal(0x12345678)
expect(r.z).to_equal(0x12345678)
expect(r.w).to_equal(0x12345678)
```

</details>

#### rotl by 1 is independent per lane: [1,2,4,8] -> [2,4,8,16]

- rotl by 1 is independent per lane: [1,2,4,8] -> [2,4,8,16]
   - Expected: r.x equals `0x00000002`
   - Expected: r.y equals `0x00000004`
   - Expected: r.z equals `0x00000008`
   - Expected: r.w equals `0x00000010`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotl by 1 is independent per lane: [1,2,4,8] -> [2,4,8,16]")
val r = simd_rotl_i32x4(_input_lanes(), 1)
expect(r.x).to_equal(0x00000002)
expect(r.y).to_equal(0x00000004)
expect(r.z).to_equal(0x00000008)
expect(r.w).to_equal(0x00000010)
```

</details>

### simd_rotr_i32x4

#### rotr by 8: 0x12345678 -> 0x78123456

- rotr by 8: 0x12345678 -> 0x78123456
   - Expected: r.x equals `0x78123456`
   - Expected: r.y equals `0x78123456`
   - Expected: r.z equals `0x78123456`
   - Expected: r.w equals `0x78123456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotr by 8: 0x12345678 -> 0x78123456")
# >> 8 = 0x00123456, << 24 = 0x78000000
val r = simd_rotr_i32x4(_input_12345678(), 8)
expect(r.x).to_equal(0x78123456)
expect(r.y).to_equal(0x78123456)
expect(r.z).to_equal(0x78123456)
expect(r.w).to_equal(0x78123456)
```

</details>

#### rotr by 16: 0x12345678 -> 0x56781234 (same as rotl by 16)

- rotr by 16: 0x12345678 -> 0x56781234 (same as rotl by 16)
   - Expected: r.x equals `0x56781234`
   - Expected: r.y equals `0x56781234`
   - Expected: r.z equals `0x56781234`
   - Expected: r.w equals `0x56781234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotr by 16: 0x12345678 -> 0x56781234 (same as rotl by 16)")
val r = simd_rotr_i32x4(_input_12345678(), 16)
expect(r.x).to_equal(0x56781234)
expect(r.y).to_equal(0x56781234)
expect(r.z).to_equal(0x56781234)
expect(r.w).to_equal(0x56781234)
```

</details>

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

- Canonical SPipe generation for source `3a8a5970995dfe553623cf8a80ecb16caac711c1903e87b95ee1c1fcdead8e77`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a8a5970995dfe553623cf8a80ecb16caac711c1903e87b95ee1c1fcdead8e77`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a8a5970995dfe553623cf8a80ecb16caac711c1903e87b95ee1c1fcdead8e77`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/simd/rotl_rotr_i32x4_spec.spl
mirror: doc/06_spec/unit/lib/simd/rotl_rotr_i32x4_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/simd/rotl_rotr_i32x4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/simd/rotl_rotr_i32x4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/simd/rotl_rotr_i32x4_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rotl by 0 is identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/simd/rotl_rotr_i32x4_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rotl by 8: 0x12345678 -> 0x34567812' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/simd/rotl_rotr_i32x4_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rotl by 16: 0x12345678 -> 0x56781234' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

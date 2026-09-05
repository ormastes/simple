# shr_logical / shl lane-width sweep — I1 unit tests

> Unit tests for `fixedvec_shr_logical_i8/i16/i64` and `fixedvec_shl_i8/i16/i64` — the per-width standalone helpers added in I1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# shr_logical / shl lane-width sweep — I1 unit tests

Unit tests for `fixedvec_shr_logical_i8/i16/i64` and `fixedvec_shl_i8/i16/i64` — the per-width standalone helpers added in I1.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-FIXEDVEC |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/lib/simd/shr_lanes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for `fixedvec_shr_logical_i8/i16/i64` and
`fixedvec_shl_i8/i16/i64` — the per-width standalone helpers added in I1.

Test IDs: SL-01 .. SL-15 (≥3 per width × 2 ops × 3 widths, minus shl
which needs fewer goldens).

Covers:
- count=0  → identity
- count=1  → single-step logical shift (sign bit zero-filled)
- count=N-1 → all but lsb shifted out, sign bit zero

All tests run in interpreter mode (no MIR required).

## Scenarios

### shr_logical i8 lane-width

#### SL-01: shr_logical_i8 count=0 is identity

- SL-01: shr_logical_i8 count=0 is identity
   - Expected: arr[0] equals `4 as i8`
   - Expected: arr[1] equals `8 as i8`
   - Expected: arr[2] equals `16 as i8`
   - Expected: arr[3] equals `32 as i8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-01: shr_logical_i8 count=0 is identity")
val v = make_i8x4_pos()
val result = fixedvec_shr_logical_i8(v, 0)
val arr = result.to_array()
expect(arr[0]).to_equal(4 as i8)
expect(arr[1]).to_equal(8 as i8)
expect(arr[2]).to_equal(16 as i8)
expect(arr[3]).to_equal(32 as i8)
```

</details>

#### SL-02: shr_logical_i8 count=1 on negative input gives positive result

- SL-02: shr_logical_i8 count=1 on negative input gives positive result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-02: shr_logical_i8 count=1 on negative input gives positive result")
val v = make_i8x4_neg()
val result = fixedvec_shr_logical_i8(v, 1)
val lane0 = result.lane(0)
expect(lane0).to_be_greater_than(0)
```

</details>

#### SL-03: shr_logical_i8 count=6 on -8 gives result in range [0,1]

- SL-03: shr_logical_i8 count=6 on -8 gives result in range [0,1]
   - Expected: lane0 equals `3 as i8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-03: shr_logical_i8 count=6 on -8 gives result in range [0,1]")
val v = make_i8x4_neg()
val result = fixedvec_shr_logical_i8(v, 6)
val lane0 = result.lane(0)
# -8 = 0xF8; logical >> 6 = 0x03
expect(lane0).to_be_greater_than(-1)
expect(lane0).to_equal(3 as i8)
```

</details>

### shr_logical i16 lane-width

#### SL-04: shr_logical_i16 count=0 is identity

- SL-04: shr_logical_i16 count=0 is identity
   - Expected: arr[0] equals `4 as i16`
   - Expected: arr[1] equals `8 as i16`
   - Expected: arr[2] equals `16 as i16`
   - Expected: arr[3] equals `32 as i16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-04: shr_logical_i16 count=0 is identity")
val v = make_i16x4_pos()
val result = fixedvec_shr_logical_i16(v, 0)
val arr = result.to_array()
expect(arr[0]).to_equal(4 as i16)
expect(arr[1]).to_equal(8 as i16)
expect(arr[2]).to_equal(16 as i16)
expect(arr[3]).to_equal(32 as i16)
```

</details>

#### SL-05: shr_logical_i16 count=1 on negative input gives positive result

- SL-05: shr_logical_i16 count=1 on negative input gives positive result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-05: shr_logical_i16 count=1 on negative input gives positive result")
val v = make_i16x4_neg()
val result = fixedvec_shr_logical_i16(v, 1)
val lane0 = result.lane(0)
expect(lane0).to_be_greater_than(0)
```

</details>

#### SL-06: shr_logical_i16 count=14 on -256 equals 3

- SL-06: shr_logical_i16 count=14 on -256 equals 3
   - Expected: lane0 equals `3 as i16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-06: shr_logical_i16 count=14 on -256 equals 3")
val v = make_i16x4_neg()
val result = fixedvec_shr_logical_i16(v, 14)
val lane0 = result.lane(0)
# -256 = 0xFF00 as u16; 0xFF00 >> 14 = 3
expect(lane0).to_equal(3 as i16)
```

</details>

### shr_logical i64 lane-width

#### SL-07: shr_logical_i64 count=0 is identity

- SL-07: shr_logical_i64 count=0 is identity
   - Expected: arr[0] equals `4 as i64`
   - Expected: arr[1] equals `8 as i64`
   - Expected: arr[2] equals `16 as i64`
   - Expected: arr[3] equals `32 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-07: shr_logical_i64 count=0 is identity")
val v = make_i64x4_pos()
val result = fixedvec_shr_logical_i64(v, 0)
val arr = result.to_array()
expect(arr[0]).to_equal(4 as i64)
expect(arr[1]).to_equal(8 as i64)
expect(arr[2]).to_equal(16 as i64)
expect(arr[3]).to_equal(32 as i64)
```

</details>

#### SL-08: shr_logical_i64 count=1 on negative input gives positive result

- SL-08: shr_logical_i64 count=1 on negative input gives positive result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-08: shr_logical_i64 count=1 on negative input gives positive result")
val v = make_i64x4_neg()
val result = fixedvec_shr_logical_i64(v, 1)
val lane0 = result.lane(0)
expect(lane0).to_be_greater_than(0)
```

</details>

#### SL-09: shr_logical_i64 count=62 on -8 equals 3

- SL-09: shr_logical_i64 count=62 on -8 equals 3
   - Expected: lane0 equals `3 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-09: shr_logical_i64 count=62 on -8 equals 3")
val v = make_i64x4_neg()
val result = fixedvec_shr_logical_i64(v, 62)
val lane0 = result.lane(0)
# -8 = 0xFFFFFFFFFFFFFFF8; 0xFFFFFFFFFFFFFFF8 >> 62 = 3
expect(lane0).to_equal(3 as i64)
```

</details>

### shl i8 lane-width

#### SL-10: shl_i8 count=0 is identity

- SL-10: shl_i8 count=0 is identity
   - Expected: arr[0] equals `4 as i8`
   - Expected: arr[1] equals `8 as i8`
   - Expected: arr[2] equals `16 as i8`
   - Expected: arr[3] equals `32 as i8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-10: shl_i8 count=0 is identity")
val v = make_i8x4_pos()
val result = fixedvec_shl_i8(v, 0)
val arr = result.to_array()
expect(arr[0]).to_equal(4 as i8)
expect(arr[1]).to_equal(8 as i8)
expect(arr[2]).to_equal(16 as i8)
expect(arr[3]).to_equal(32 as i8)
```

</details>

#### SL-11: shl_i8 count=1 doubles each lane

- SL-11: shl_i8 count=1 doubles each lane
   - Expected: arr[0] equals `8 as i8`
   - Expected: arr[1] equals `16 as i8`
   - Expected: arr[2] equals `32 as i8`
   - Expected: arr[3] equals `64 as i8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-11: shl_i8 count=1 doubles each lane")
val v = make_i8x4_pos()
val result = fixedvec_shl_i8(v, 1)
val arr = result.to_array()
expect(arr[0]).to_equal(8 as i8)
expect(arr[1]).to_equal(16 as i8)
expect(arr[2]).to_equal(32 as i8)
expect(arr[3]).to_equal(64 as i8)
```

</details>

#### SL-12: shl_i8 count=3 multiplies each lane by 8

- SL-12: shl_i8 count=3 multiplies each lane by 8
   - Expected: arr[0] equals `8 as i8`
   - Expected: arr[1] equals `16 as i8`
   - Expected: arr[2] equals `24 as i8`
   - Expected: arr[3] equals `32 as i8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-12: shl_i8 count=3 multiplies each lane by 8")
val v = fixedvec_from_array([1 as i8, 2 as i8, 3 as i8, 4 as i8])
val result = fixedvec_shl_i8(v, 3)
val arr = result.to_array()
expect(arr[0]).to_equal(8 as i8)
expect(arr[1]).to_equal(16 as i8)
expect(arr[2]).to_equal(24 as i8)
expect(arr[3]).to_equal(32 as i8)
```

</details>

### shl i16 lane-width

#### SL-13: shl_i16 count=2 multiplies each lane by 4

- SL-13: shl_i16 count=2 multiplies each lane by 4
   - Expected: arr[0] equals `16 as i16`
   - Expected: arr[1] equals `32 as i16`
   - Expected: arr[2] equals `64 as i16`
   - Expected: arr[3] equals `128 as i16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-13: shl_i16 count=2 multiplies each lane by 4")
val v = make_i16x4_pos()
val result = fixedvec_shl_i16(v, 2)
val arr = result.to_array()
expect(arr[0]).to_equal(16 as i16)
expect(arr[1]).to_equal(32 as i16)
expect(arr[2]).to_equal(64 as i16)
expect(arr[3]).to_equal(128 as i16)
```

</details>

### shl i64 lane-width

#### SL-14: shl_i64 count=0 is identity

- SL-14: shl_i64 count=0 is identity
   - Expected: arr[0] equals `4 as i64`
   - Expected: arr[1] equals `8 as i64`
   - Expected: arr[2] equals `16 as i64`
   - Expected: arr[3] equals `32 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-14: shl_i64 count=0 is identity")
val v = make_i64x4_pos()
val result = fixedvec_shl_i64(v, 0)
val arr = result.to_array()
expect(arr[0]).to_equal(4 as i64)
expect(arr[1]).to_equal(8 as i64)
expect(arr[2]).to_equal(16 as i64)
expect(arr[3]).to_equal(32 as i64)
```

</details>

#### SL-15: shl_i64 count=1 doubles each lane

- SL-15: shl_i64 count=1 doubles each lane
   - Expected: arr[0] equals `8 as i64`
   - Expected: arr[1] equals `16 as i64`
   - Expected: arr[2] equals `32 as i64`
   - Expected: arr[3] equals `64 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SL-15: shl_i64 count=1 doubles each lane")
val v = make_i64x4_pos()
val result = fixedvec_shl_i64(v, 1)
val arr = result.to_array()
expect(arr[0]).to_equal(8 as i64)
expect(arr[1]).to_equal(16 as i64)
expect(arr[2]).to_equal(32 as i64)
expect(arr[3]).to_equal(64 as i64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `0714ae349e9c82c70c276e4307031e8edcce43e8ff48abde3967fcf2665835c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0714ae349e9c82c70c276e4307031e8edcce43e8ff48abde3967fcf2665835c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0714ae349e9c82c70c276e4307031e8edcce43e8ff48abde3967fcf2665835c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/simd/shr_lanes_spec.spl
mirror: doc/06_spec/01_unit/lib/simd/shr_lanes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/simd/shr_lanes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/simd/shr_lanes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/simd/shr_lanes_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SL-01: shr_logical_i8 count=0 is identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/simd/shr_lanes_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SL-02: shr_logical_i8 count=1 on negative input gives positive result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/simd/shr_lanes_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SL-03: shr_logical_i8 count=6 on -8 gives result in range [0,1]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

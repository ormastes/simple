# shr_logical / shl lane-width sweep — I1 unit tests

> Unit tests for `fixedvec_shr_logical_i8/i16/i64` and `fixedvec_shl_i8/i16/i64` — the per-width standalone helpers added in I1.

<!-- sdn-diagram:id=shr_lanes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shr_lanes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shr_lanes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shr_lanes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_i8x4_neg()
val result = fixedvec_shr_logical_i8(v, 1)
val lane0 = result.lane(0)
expect(lane0).to_be_greater_than(0)
```

</details>

#### SL-03: shr_logical_i8 count=6 on -8 gives result in range [0,1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_i16x4_neg()
val result = fixedvec_shr_logical_i16(v, 1)
val lane0 = result.lane(0)
expect(lane0).to_be_greater_than(0)
```

</details>

#### SL-06: shr_logical_i16 count=14 on -256 equals 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_i16x4_neg()
val result = fixedvec_shr_logical_i16(v, 14)
val lane0 = result.lane(0)
# -256 = 0xFF00 as u16; 0xFF00 >> 14 = 3
expect(lane0).to_equal(3 as i16)
```

</details>

### shr_logical i64 lane-width

#### SL-07: shr_logical_i64 count=0 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_i64x4_neg()
val result = fixedvec_shr_logical_i64(v, 1)
val lane0 = result.lane(0)
expect(lane0).to_be_greater_than(0)
```

</details>

#### SL-09: shr_logical_i64 count=62 on -8 equals 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_i64x4_neg()
val result = fixedvec_shr_logical_i64(v, 62)
val lane0 = result.lane(0)
# -8 = 0xFFFFFFFFFFFFFFF8; 0xFFFFFFFFFFFFFFF8 >> 62 = 3
expect(lane0).to_equal(3 as i64)
```

</details>

### shl i8 lane-width

#### SL-10: shl_i8 count=0 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

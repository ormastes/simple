# rotl_rotr_i32x4_spec

> Rotate-left wrapper over simd_shl_i32x4, simd_shr_i32x4, simd_or_i32x4.

<!-- sdn-diagram:id=rotl_rotr_i32x4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rotl_rotr_i32x4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rotl_rotr_i32x4_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rotl_rotr_i32x4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/simd/rotl_rotr_i32x4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Rotate-left wrapper over simd_shl_i32x4, simd_shr_i32x4, simd_or_i32x4.
    Test vectors derived from RFC 7539 rotation amounts and hand-computed values.

## Scenarios

### simd_rotl_i32x4

#### rotl by 0 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = simd_rotl_i32x4(_input_12345678(), 0)
expect(r.x).to_equal(0x12345678)
expect(r.y).to_equal(0x12345678)
expect(r.z).to_equal(0x12345678)
expect(r.w).to_equal(0x12345678)
```

</details>

#### rotl by 8: 0x12345678 -> 0x34567812

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = simd_rotl_i32x4(_input_12345678(), 8)
expect(r.x).to_equal(0x34567812)
expect(r.y).to_equal(0x34567812)
expect(r.z).to_equal(0x34567812)
expect(r.w).to_equal(0x34567812)
```

</details>

#### rotl by 16: 0x12345678 -> 0x56781234

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = simd_rotl_i32x4(_input_12345678(), 16)
expect(r.x).to_equal(0x56781234)
expect(r.y).to_equal(0x56781234)
expect(r.z).to_equal(0x56781234)
expect(r.w).to_equal(0x56781234)
```

</details>

#### rotl by 31: 0x12345678 -> 0x091a2b3c

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x12345678 << 31 = 0 (bit 0 of 0x78 = 0), >> 1 = 0x091A2B3C
val r = simd_rotl_i32x4(_input_12345678(), 31)
expect(r.x).to_equal(0x091a2b3c)
expect(r.y).to_equal(0x091a2b3c)
expect(r.z).to_equal(0x091a2b3c)
expect(r.w).to_equal(0x091a2b3c)
```

</details>

#### rotl by 32 is identity (n masked to 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = simd_rotl_i32x4(_input_12345678(), 32)
expect(r.x).to_equal(0x12345678)
expect(r.y).to_equal(0x12345678)
expect(r.z).to_equal(0x12345678)
expect(r.w).to_equal(0x12345678)
```

</details>

#### rotl by 1 is independent per lane: [1,2,4,8] -> [2,4,8,16]

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = simd_rotl_i32x4(_input_lanes(), 1)
expect(r.x).to_equal(0x00000002)
expect(r.y).to_equal(0x00000004)
expect(r.z).to_equal(0x00000008)
expect(r.w).to_equal(0x00000010)
```

</details>

### simd_rotr_i32x4

#### rotr by 8: 0x12345678 -> 0x78123456

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# >> 8 = 0x00123456, << 24 = 0x78000000
val r = simd_rotr_i32x4(_input_12345678(), 8)
expect(r.x).to_equal(0x78123456)
expect(r.y).to_equal(0x78123456)
expect(r.z).to_equal(0x78123456)
expect(r.w).to_equal(0x78123456)
```

</details>

#### rotr by 16: 0x12345678 -> 0x56781234 (same as rotl by 16)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

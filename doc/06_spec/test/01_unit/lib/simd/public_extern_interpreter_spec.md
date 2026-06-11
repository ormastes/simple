# Public Extern Interpreter Specification

> <details>

<!-- sdn-diagram:id=public_extern_interpreter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=public_extern_interpreter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

public_extern_interpreter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=public_extern_interpreter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Public Extern Interpreter Specification

## Scenarios

### public SIMD externs in interpreter mode

#### executes u32x4 arithmetic and bitwise externs

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/simd/public_extern_interpreter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

# SIMD f32 Intrinsics Specification

> Validates the interpreter-visible f32 SIMD facade used by the science backend

<!-- sdn-diagram:id=simd_f32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simd_f32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simd_f32_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simd_f32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SIMD f32 Intrinsics Specification

Validates the interpreter-visible f32 SIMD facade used by the science backend

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-C-001, REQ-SCILIB-C-004, NFR-SCILIB-C-001, NFR-SCILIB-C-002 |
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/simd_f32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the interpreter-visible f32 SIMD facade used by the science backend
extension plan. These are explicit SIMD probes, not automatic ndarray backend
dispatch.

## Scenarios

### SIMD f32x4 arithmetic

#### computes lane-wise add/sub/mul/div

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec8f(e0: 1.0, e1: 2.0, e2: 3.0, e3: 4.0, e4: 5.0, e5: 6.0, e6: 7.0, e7: 8.0)
val b = Vec8f(e0: 8.0, e1: 7.0, e2: 6.0, e3: 5.0, e4: 4.0, e5: 3.0, e6: 2.0, e7: 1.0)
val c = Vec8f.splat(1.0)
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

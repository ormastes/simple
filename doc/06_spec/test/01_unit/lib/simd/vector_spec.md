# Vector Trait Unit Tests — Trait Surface (D5 kickoff)

> Unit tests for the `Vector` trait abstraction: generic functions bounded by `Vector`, lane count query, and splat through concrete implementations. Corresponds to D5 trait-surface kickoff test IDs V-01 through V-03.

<!-- sdn-diagram:id=vector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vector_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Trait Unit Tests — Trait Surface (D5 kickoff)

Unit tests for the `Vector` trait abstraction: generic functions bounded by `Vector`, lane count query, and splat through concrete implementations. Corresponds to D5 trait-surface kickoff test IDs V-01 through V-03.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-VECTOR |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Design | doc/04_architecture/simd_unified_architecture_detail.md §1.1 |
| Source | `test/01_unit/lib/simd/vector_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for the `Vector` trait abstraction: generic functions bounded by
`Vector`, lane count query, and splat through concrete implementations.
Corresponds to D5 trait-surface kickoff test IDs V-01 through V-03.

Uses back-compat aliases (C2 §11.3): Vec4f = FixedVec<f32,4>,
Vec4i = FixedVec<i32,4>, Vec8i = FixedVec<i32,8> — avoids parser limitation
with integer const-generic arguments in type-expression position.

Per C2 §1.1: `Vector` has NO constructors — splat lives on the concrete type.
V-03 calls `Vec4i.splat(7)` (not a hypothetical `Vector.splat`).

All tests run in interpreter mode. Expected result before D4 lands:
0 passing (import resolution fails). After D4 lands: 3/3 passing.

## Scenarios

### Vector trait abstraction

#### V-01: generic add via Vector trait doubles each lane for f32x4 and i32x8

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# f32x4: [1,2,3,4] doubled = [2,4,6,8]
val vf = Vec4f.from_array([1.0, 2.0, 3.0, 4.0])
val doubled_f = double_f32x4(vf)
val arr_f = doubled_f.to_array()
expect(arr_f[0]).to_equal(2.0)
expect(arr_f[1]).to_equal(4.0)
expect(arr_f[2]).to_equal(6.0)
expect(arr_f[3]).to_equal(8.0)

# i32x8: [1,2,3,4,5,6,7,8] doubled = [2,4,6,8,10,12,14,16]
val vi = Vec8i.from_array([1, 2, 3, 4, 5, 6, 7, 8])
val doubled_i = double_i32x8(vi)
val arr_i = doubled_i.to_array()
expect(arr_i[0]).to_equal(2)
expect(arr_i[7]).to_equal(16)
```

</details>

#### V-02: lanes() via Vector trait returns N for FixedVec

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vf = Vec4f.splat(0.0)
val cf = lane_count_f32x4(vf)
expect(cf).to_equal(4)

val vi = Vec8i.splat(0)
val ci = lane_count_i32x8(vi)
expect(ci).to_equal(8)
```

</details>

#### V-03: Vec4i.splat(7) produces four lanes of 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec4i.splat(7)
val arr = v.to_array()
expect(arr[0]).to_equal(7)
expect(arr[1]).to_equal(7)
expect(arr[2]).to_equal(7)
expect(arr[3]).to_equal(7)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/04_architecture/simd_unified_architecture_detail.md §1.1](doc/04_architecture/simd_unified_architecture_detail.md §1.1)


</details>

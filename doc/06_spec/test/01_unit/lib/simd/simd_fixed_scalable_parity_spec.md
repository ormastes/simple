# Fixed/Scalable SIMD Parity + Adapter Tests

> Asserts that FixedVec<T> and ScalableVec<T> produce numerically equivalent results for shared operations when given identical inputs (parity).

<!-- sdn-diagram:id=simd_fixed_scalable_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simd_fixed_scalable_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simd_fixed_scalable_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simd_fixed_scalable_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed/Scalable SIMD Parity + Adapter Tests

Asserts that FixedVec<T> and ScalableVec<T> produce numerically equivalent results for shared operations when given identical inputs (parity).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-SCALABLE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Active |
| Design | doc/05_design/simd_fixed_and_scalable_vectors.md |
| Source | `test/01_unit/lib/simd/simd_fixed_scalable_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Asserts that FixedVec<T> and ScalableVec<T> produce numerically equivalent
results for shared operations when given identical inputs (parity).

Also covers the ScalableAdapter lowering-diagnostics surface
(scalable_lower_f32, diag_is_ok, diag_is_split, diag_is_pad, diag_note)
using the real library — no inline redefinitions.

## Scenarios

### FixedVec / ScalableVec arithmetic parity

#### P-01: add produces same lane values for f32

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fi = make_fixed_i32()
val si = make_scalable_i32()
expect(fi.reduce_sum()).to_equal(si.reduce_sum())
```

</details>

#### P-05: reduce_min and reduce_max agree for i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fi = make_fixed_i32()
val si = make_scalable_i32()
expect(fi.reduce_min()).to_equal(si.reduce_min())
expect(fi.reduce_max()).to_equal(si.reduce_max())
```

</details>

#### P-06: splat parity — same value in every lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fv = fixedvec_splat(7.0, 4)
val sv = scalablevec_splat(7.0)
expect(fv.lane(0)).to_equal(sv.lane(0))
expect(fv.lane(3)).to_equal(sv.lane(3))
```

</details>

#### P-07: from_fixed round-trip preserves all lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = scalable_lower_f32(4, 4)
expect(diag_is_ok(d)).to_equal(true)
expect(diag_note(d)).to_equal("direct map")
```

</details>

#### A-02: split required when fixed lanes exceed target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = scalable_lower_f32(8, 4)
expect(diag_is_split(d)).to_equal(true)
expect(diag_note(d)).to_equal("split required")
```

</details>

#### A-03: padding required when fixed lanes less than target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = scalable_lower_f32(4, 8)
expect(diag_is_pad(d)).to_equal(true)
expect(diag_note(d)).to_equal("padding required")
```

</details>

#### A-04: kind constants are distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lowering_ok()).to_equal(0)
expect(lowering_split()).to_equal(1)
expect(lowering_pad()).to_equal(2)
```

</details>

#### A-05: fixed_lanes and target_lanes fields are preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = scalable_lower_f32(8, 4)
expect(d.fixed_lanes).to_equal(8)
expect(d.target_lanes).to_equal(4)
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

- **Design:** [doc/05_design/simd_fixed_and_scalable_vectors.md](doc/05_design/simd_fixed_and_scalable_vectors.md)


</details>

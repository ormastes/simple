# ScalableVec<T> Unit Tests

> Executable coverage for the interpreter-visible `ScalableVec<T>` surface. This replaces the earlier compatibility anchor now that `ScalableVec` construction and methods are callable from spec code.

<!-- sdn-diagram:id=scalable_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scalable_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scalable_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scalable_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ScalableVec<T> Unit Tests

Executable coverage for the interpreter-visible `ScalableVec<T>` surface. This replaces the earlier compatibility anchor now that `ScalableVec` construction and methods are callable from spec code.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-SCALABLE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Design | doc/05_design/simd_fixed_and_scalable_vectors.md |
| Source | `test/01_unit/lib/simd/scalable_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Executable coverage for the interpreter-visible `ScalableVec<T>` surface.
This replaces the earlier compatibility anchor now that `ScalableVec`
construction and methods are callable from spec code.

## Scenarios

### ScalableVec construction and arithmetic

#### S-01: splat uses the architectural minimum lane count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = scalablevec_splat(1.5)
expect(v.lanes()).to_equal(scalablevec_min_lanes())
expect(v.lane(0)).to_equal(1.5)
expect(v.lane(3)).to_equal(1.5)
```

</details>

#### S-02: splat_n creates runtime-sized vectors and zero-values remain explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val splat = scalablevec_splat_n(9, 6)
expect(splat.lanes()).to_equal(6)
expect(splat.lane(5)).to_equal(9)

val zero = scalablevec_splat_n(0, scalablevec_min_lanes())
expect(zero.lanes()).to_equal(4)
expect(zero.lane(0)).to_equal(0)
expect(zero.lane(3)).to_equal(0)
```

</details>

#### S-03: lane access, set_lane, from_array, and to_array are callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = scalablevec_from_array([1.0, 2.0, 3.0, 4.0, 5.0])
expect(v.lanes()).to_equal(5)
expect(v.lane(1)).to_equal(2.0)

val updated = v.set_lane(3, 99.0)
val arr = updated.to_array()
expect(arr[0]).to_equal(1.0)
expect(arr[3]).to_equal(99.0)
expect(arr[4]).to_equal(5.0)
```

</details>

#### S-04: add, sub, mul, and div operate lane-wise

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lhs = make_scalable_1234()
val rhs = make_scalable_rhs()

val add = lhs.add(rhs).to_array()
expect(add[0]).to_equal(11.0)
expect(add[3]).to_equal(44.0)

val sub = rhs.sub(lhs).to_array()
expect(sub[0]).to_equal(9.0)
expect(sub[3]).to_equal(36.0)

val mul = lhs.mul(scalablevec_from_array([2.0, 3.0, 4.0, 5.0])).to_array()
expect(mul[0]).to_equal(2.0)
expect(mul[3]).to_equal(20.0)

val div = rhs.div(scalablevec_from_array([2.0, 4.0, 5.0, 8.0])).to_array()
expect(div[0]).to_equal(5.0)
expect(div[3]).to_equal(5.0)
```

</details>

#### S-05: min, max, reductions, and comparisons preserve scalable semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ints = make_scalable_i32()
val rhs = scalablevec_from_array([2, 4, 8, 6])

val min_arr = ints.min(rhs).to_array()
expect(min_arr[0]).to_equal(1)
expect(min_arr[2]).to_equal(2)

val max_arr = ints.max(rhs).to_array()
expect(max_arr[1]).to_equal(5)
expect(max_arr[2]).to_equal(8)

expect(ints.reduce_sum()).to_equal(15)
expect(ints.reduce_min()).to_equal(1)
expect(ints.reduce_max()).to_equal(7)

val mask = ints.cmp_gt(rhs)
expect(mask.lane_active(0)).to_equal(false)
expect(mask.lane_active(1)).to_equal(true)
expect(mask.lane_active(2)).to_equal(false)
expect(mask.lane_active(3)).to_equal(true)
```

</details>

#### S-06: from_fixed always succeeds and try_to_fixed is explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixed = fixedvec_from_array([1.0, 2.0, 3.0, 4.0])
val scalable = scalablevec_from_fixed(fixed)
expect(scalable.lanes()).to_equal(4)
expect(scalable.lane(2)).to_equal(3.0)

val narrowed = scalable.try_to_fixed(4)
expect(narrowed.is_some()).to_equal(true)
expect(narrowed.unwrap().lane(3)).to_equal(4.0)

val mismatch = scalable.try_to_fixed(8)
expect(mismatch.is_none()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/simd_fixed_and_scalable_vectors.md](doc/05_design/simd_fixed_and_scalable_vectors.md)


</details>

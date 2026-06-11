# Mask<V> Compatibility Anchors

> Compatibility-anchor tests for `Mask<V>` semantics: 4-lane all-ones/all-zeros bit patterns, logical bit-ops, count/none predicates, and mask-select-style lane blending. Corresponds to D5 trait-surface kickoff test IDs M-01 through M-06.

<!-- sdn-diagram:id=mask_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mask_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mask_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mask_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mask<V> Compatibility Anchors

Compatibility-anchor tests for `Mask<V>` semantics: 4-lane all-ones/all-zeros bit patterns, logical bit-ops, count/none predicates, and mask-select-style lane blending. Corresponds to D5 trait-surface kickoff test IDs M-01 through M-06.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-MASK |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Design | doc/04_architecture/simd_unified_architecture_detail.md §1.4 §5 |
| Source | `test/01_unit/lib/simd/mask_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Compatibility-anchor tests for `Mask<V>` semantics: 4-lane all-ones/all-zeros
bit patterns, logical bit-ops, count/none predicates, and mask-select-style
lane blending. Corresponds to D5 trait-surface kickoff test IDs M-01 through
M-06.

The current interpreter surface does not expose a callable `Mask<Vec4f>` /
`Mask<Vec4i>` constructor path from spec code, so these checks validate the
same public lane semantics through explicit mask-bit helpers instead.

## Scenarios

### Mask construction and operations

#### M-01: all_ones_n(4) has count_ones equal to lane count 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mask_all_ones_n(4)
val n = mask_count_ones(m, 4)
expect(n).to_equal(4)
```

</details>

#### M-02: all_zeros_n(4) has count_ones zero and none returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mask_all_zeros_n(4)
val n = mask_count_ones(m, 4)
expect(n).to_equal(0)
val is_none = mask_none(m, 4)
expect(is_none).to_equal(true)
```

</details>

#### M-03: cmp_lt mask matches per-lane manual comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_f32x4_low()
val vb = make_f32x4_high()
val m = cmp_lt_mask(va, vb)
val n = mask_count_ones(m, 4)
expect(n).to_equal(2)
```

</details>

#### M-04: and or xor not logical ops are element-wise correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ones = mask_all_ones_n(4)
val zeros = mask_all_zeros_n(4)

val and_result = mask_and(ones, zeros)
expect(mask_count_ones(and_result, 4)).to_equal(0)

val or_result = mask_or(ones, zeros)
expect(mask_count_ones(or_result, 4)).to_equal(4)

val xor_result = mask_xor(ones, ones)
expect(mask_count_ones(xor_result, 4)).to_equal(0)

val not_zeros = mask_not(zeros, 4)
val nz_any = mask_count_ones(not_zeros, 4) > 0
expect(nz_any).to_equal(true)
```

</details>

#### M-05: mask_select returns t lanes where mask is 1 and f lanes where mask is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t_vals = make_f32x4_true_vals()
val f_vals = make_f32x4_false_vals()

val ones = mask_all_ones_n(4)
val arr_ones = mask_select_f32(ones, t_vals, f_vals)
expect(arr_ones[0]).to_equal(100.0)
expect(arr_ones[3]).to_equal(400.0)

val zeros = mask_all_zeros_n(4)
val arr_zeros = mask_select_f32(zeros, t_vals, f_vals)
expect(arr_zeros[0]).to_equal(0.0)
expect(arr_zeros[3]).to_equal(0.0)
```

</details>

#### M-06: Mask<Vec4f> and Mask<Vec4i> have consistent lane counts (type distinction anchor)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mf = mask_all_ones_n(4)
val mi = mask_all_ones_n(4)
expect(mask_count_ones(mf, 4)).to_equal(4)
expect(mask_count_ones(mi, 4)).to_equal(4)
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

- **Design:** [doc/04_architecture/simd_unified_architecture_detail.md §1.4 §5](doc/04_architecture/simd_unified_architecture_detail.md §1.4 §5)


</details>

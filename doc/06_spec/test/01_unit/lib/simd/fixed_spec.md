# FixedVec<T,N> Unit Tests — Trait Surface (D5 kickoff)

> Unit tests for `FixedVec<T,N>` construction, arithmetic, reductions, lane access, lane-count validation, and shift semantics. Corresponds to D5 trait-surface kickoff test IDs F-01 through F-10.

<!-- sdn-diagram:id=fixed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixed_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FixedVec<T,N> Unit Tests — Trait Surface (D5 kickoff)

Unit tests for `FixedVec<T,N>` construction, arithmetic, reductions, lane access, lane-count validation, and shift semantics. Corresponds to D5 trait-surface kickoff test IDs F-01 through F-10.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-FIXEDVEC |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Plan | doc/05_design/simd_rollout_plan.md |
| Design | doc/04_architecture/simd_unified_architecture_detail.md |
| Source | `test/01_unit/lib/simd/fixed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for `FixedVec<T,N>` construction, arithmetic, reductions,
lane access, lane-count validation, and shift semantics. Corresponds to
D5 trait-surface kickoff test IDs F-01 through F-10.

Uses back-compat wrapper functions (C2 §11.3): vec4f_splat(), fixedvec_from_array(), etc.
Returns FixedVec<f32>/FixedVec<i32> directly — avoids parser limitation with
integer const-generic arguments in type-expression position.

All tests run in interpreter mode.

Current status (D4 partial): F-01, F-02, F-09 pass (3/10).
F-03..F-08, F-10 fail with "method not found on Vec4f/Vec4i" — trait
impl methods from `impl FixedVec with Vector` are not resolved through
type aliases (e.g. `Vec4f = FixedVec<f32,4>`) in interpreter mode.
Root cause: D3 type-IR gap — type alias expansion for trait impl lookup
not yet wired. See feedback_simd_trait_alias_gap.md.

## Scenarios

### FixedVec construction and basic ops

#### F-01: splat(0.0) produces all-zero 4-lane f32 vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = vec4f_splat(0.0)
val arr = v.to_array()
expect(arr[0]).to_equal(0.0)
expect(arr[1]).to_equal(0.0)
expect(arr[2]).to_equal(0.0)
expect(arr[3]).to_equal(0.0)
```

</details>

#### F-02: from_array to_array round-trip preserves all lane values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_f32x4_1234()
val arr = v.to_array()
expect(arr[0]).to_equal(1.0)
expect(arr[1]).to_equal(2.0)
expect(arr[2]).to_equal(3.0)
expect(arr[3]).to_equal(4.0)
```

</details>

#### F-03: add is element-wise for f32x4

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_f32x4_1234()
val vb = make_f32x4_add_rhs()
val result = va.add(vb)
val arr = result.to_array()
expect(arr[0]).to_equal(11.0)
expect(arr[1]).to_equal(22.0)
expect(arr[2]).to_equal(33.0)
expect(arr[3]).to_equal(44.0)
```

</details>

#### F-04: mul is element-wise for f32x4

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_f32x4_1234()
val vb = make_f32x4_mul_rhs()
val result = va.mul(vb)
val arr = result.to_array()
expect(arr[0]).to_equal(2.0)
expect(arr[1]).to_equal(6.0)
expect(arr[2]).to_equal(12.0)
expect(arr[3]).to_equal(20.0)
```

</details>

#### F-05: fma computes self*b+c element-wise for f32x4

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_f32x4_1234()
val vb = make_f32x4_mul_rhs()
val vc = make_f32x4_add_rhs()
val result = va.fma(vb, vc)
val arr = result.to_array()
expect(arr[0]).to_equal(12.0)
expect(arr[1]).to_equal(26.0)
expect(arr[2]).to_equal(42.0)
expect(arr[3]).to_equal(60.0)
```

</details>

#### F-06: reduce_sum of [1.0 2.0 3.0 4.0] equals 10.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_f32x4_1234()
val s = v.reduce_sum()
expect(s).to_equal(10.0)
```

</details>

#### F-07: reduce_max of [3.0 1.0 4.0 1.0] equals 4.0 (finite values)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_f32x4_3141()
val m = v.reduce_max()
expect(m).to_equal(4.0)
```

</details>

#### F-08: lane and set_lane access and replace individual lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = make_f32x4_1234()
# Read lane 1 (should be 2.0)
val lane1 = v.lane(1)
expect(lane1).to_equal(2.0)
# Replace lane 2 with 99.0 and read back
val v2 = v.set_lane(2, 99.0)
val lane2 = v2.lane(2)
expect(lane2).to_equal(99.0)
# Other lanes untouched
val lane0 = v2.lane(0)
expect(lane0).to_equal(1.0)
```

</details>

#### F-09: E_SIMD_BAD_LANES lane-count constraint documentation anchor

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# C2 §1.0 / §2.1: N must be in {2,4,8,16,32,64}.
val n = 3
val valid_ns = [2, 4, 8, 16, 32, 64]
var found = false
var i = 0
while i < 6:
    if valid_ns[i] == n:
        found = true
    i = i + 1
expect(found).to_equal(false)
```

</details>

#### F-10: shr_logical and shr_arith differ on negative i32 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vneg = make_i32x4_neg()
val logical = vneg.shr_logical(1)
val arith   = vneg.shr_arith(1)
# shr_logical result is non-negative (high bit cleared)
val lg0 = logical.lane(0)
expect(lg0).to_be_greater_than(0)
# shr_arith result preserves sign (remains negative = -4)
val ar0 = arith.lane(0)
expect(ar0).to_equal(-4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/05_design/simd_rollout_plan.md](doc/05_design/simd_rollout_plan.md)
- **Design:** [doc/04_architecture/simd_unified_architecture_detail.md](doc/04_architecture/simd_unified_architecture_detail.md)


</details>

# FixedVec<f32,4> Cross-Target Equivalence Tests — M0

> Proves that `FixedVec<f32,4>` arithmetic (add, mul, fma, max, min, sub, neg, reduce_min) produces bit-identical results to a scalar reference implementation.

<!-- sdn-diagram:id=cross_target_simd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cross_target_simd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cross_target_simd_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cross_target_simd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FixedVec<f32,4> Cross-Target Equivalence Tests — M0

Proves that `FixedVec<f32,4>` arithmetic (add, mul, fma, max, min, sub, neg, reduce_min) produces bit-identical results to a scalar reference implementation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SIMD-CROSS-TARGET |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Active |
| Design | doc/05_design/simd_test_catalog.md §6 (T3 — Cross-Target Equivalence) |
| Source | `test/01_unit/lib/simd/cross_target_simd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves that `FixedVec<f32,4>` arithmetic (add, mul, fma, max, min, sub, neg,
reduce_min) produces bit-identical results to a scalar reference implementation.

## f32 Equality Policy

All test inputs are exact-representation f32 values (integers and dyadic fractions
with |value| < 2^24).  For such inputs, bit-equality holds unconditionally across
backends because:
- add/sub/mul/max/min: IEEE 754 requires identical rounding for operands whose
  mathematical result is also exactly representable.
- fma: single-rounded FMA equals double-rounded (a*b + c) iff the intermediate
  product a*b is exactly representable.  All FMA inputs here satisfy |a*b| < 2^24,
  so both rounding modes agree bit-for-bit.

No `to_be_close` or ULP tolerance is needed or used.

## Cross-Target Reuse

This file may be run verbatim on any host (x86, ARM, RISC-V).  Each test computes
expected values via per-element scalar arithmetic in Simple — no arch-specific
constants.  When a different backend is selected, the assertions remain identical.

## Construction Note

Uses `vec4f_from_array` wrapper function (C2 §11.3).  Direct
`Vec4f` alias form is inert until D3/E2 lands — see aliases.spl.

## Test input vectors (shared across all tests)

    a = [1.0, 2.0, 4.0, 0.25]   — dyadic fractions, exact f32
    b = [3.0, 0.5, 2.0, 8.0]    — dyadic fractions, exact f32
    c = [0.25, 1.0, -3.5, 2.0]  — mixed sign, exact f32 (vc[2] negative for abs/neg tests)

## Scenarios

### FixedVec<f32,4> cross-target equivalence — add

#### CT-01: add matches scalar reference for all four lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_va()
val vb = make_vb()
val result = va.add(vb)
val got = result.to_array()
# Scalar reference (double-checked): 1+3=4, 2+0.5=2.5, 4+2=6, 0.25+8=8.25
expect(got[0]).to_equal(4.0)
expect(got[1]).to_equal(2.5)
expect(got[2]).to_equal(6.0)
expect(got[3]).to_equal(8.25)
```

</details>

### FixedVec<f32,4> cross-target equivalence — mul

#### CT-02: mul matches scalar reference for all four lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_va()
val vb = make_vb()
val result = va.mul(vb)
val got = result.to_array()
# Scalar reference: 1*3=3, 2*0.5=1, 4*2=8, 0.25*8=2
expect(got[0]).to_equal(3.0)
expect(got[1]).to_equal(1.0)
expect(got[2]).to_equal(8.0)
expect(got[3]).to_equal(2.0)
```

</details>

### FixedVec<f32,4> cross-target equivalence — fma

#### CT-03: fma matches scalar reference for all four lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_va()
val vb = make_vb()
val vc = make_vc()
val result = va.fma(vb, vc)
val got = result.to_array()
# Scalar reference: 1*3+0.25=3.25, 2*0.5+1=2, 4*2+(-3.5)=4.5, 0.25*8+2=4
expect(got[0]).to_equal(3.25)
expect(got[1]).to_equal(2.0)
expect(got[2]).to_equal(4.5)
expect(got[3]).to_equal(4.0)
```

</details>

### FixedVec<f32,4> cross-target equivalence — max

#### CT-04: max matches scalar reference for all four lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_va()
val vb = make_vb()
val result = va.max(vb)
val got = result.to_array()
# Scalar reference: max(1,3)=3, max(2,0.5)=2, max(4,2)=4, max(0.25,8)=8
expect(got[0]).to_equal(3.0)
expect(got[1]).to_equal(2.0)
expect(got[2]).to_equal(4.0)
expect(got[3]).to_equal(8.0)
```

</details>

### FixedVec<f32,4> cross-target equivalence — min

#### CT-05: min matches scalar reference for all four lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_va()
val vb = make_vb()
val result = va.min(vb)
val got = result.to_array()
# Scalar reference: min(1,3)=1, min(2,0.5)=0.5, min(4,2)=2, min(0.25,8)=0.25
expect(got[0]).to_equal(1.0)
expect(got[1]).to_equal(0.5)
expect(got[2]).to_equal(2.0)
expect(got[3]).to_equal(0.25)
```

</details>

### FixedVec<f32,4> cross-target equivalence — abs

#### CT-06: abs matches scalar reference for all four lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vc = make_vc()
val result = vc.abs()
val got = result.to_array()
expect(got[0]).to_equal(0.25)
expect(got[1]).to_equal(1.0)
expect(got[2]).to_equal(3.5)
expect(got[3]).to_equal(2.0)
```

</details>

### FixedVec<f32,4> cross-target equivalence — reduce_min

#### CT-07: reduce_min matches scalar reference minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_va()
val result = va.reduce_min()
expect(result).to_equal(0.25)
```

</details>

### FixedVec<f32,4> cross-target equivalence — sub

#### CT-08: sub matches scalar reference for all four lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_va()
val vb = make_vb()
val result = va.sub(vb)
val got = result.to_array()
# Scalar reference: 1-3=-2, 2-0.5=1.5, 4-2=2, 0.25-8=-7.75
expect(got[0]).to_equal(-2.0)
expect(got[1]).to_equal(1.5)
expect(got[2]).to_equal(2.0)
expect(got[3]).to_equal(-7.75)
```

</details>

### FixedVec<f32,4> cross-target equivalence — neg

#### CT-09: neg matches scalar reference for all four lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = make_va()
val result = va.neg()
val got = result.to_array()
# Scalar reference: -1, -2, -4, -0.25
expect(got[0]).to_equal(-1.0)
expect(got[1]).to_equal(-2.0)
expect(got[2]).to_equal(-4.0)
expect(got[3]).to_equal(-0.25)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/simd_test_catalog.md §6 (T3 — Cross-Target Equivalence)](doc/05_design/simd_test_catalog.md §6 (T3 — Cross-Target Equivalence))


</details>

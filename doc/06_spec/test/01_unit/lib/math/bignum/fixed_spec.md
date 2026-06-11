# Fixed Specification

> <details>

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
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed Specification

## Scenarios

### math.bignum.fixed

### constructors

#### fx_zero(3) is three zero limbs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = fx_zero(3)
expect(z.n).to_equal(3)
expect(z.limbs[0]).to_equal(0)
expect(z.limbs[1]).to_equal(0)
expect(z.limbs[2]).to_equal(0)
```

</details>

#### fx_one(3) is [1, 0, 0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = fx_one(3)
expect(o.limbs[0]).to_equal(1)
expect(o.limbs[1]).to_equal(0)
expect(o.limbs[2]).to_equal(0)
```

</details>

#### fx_clone is a deep copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [11, 22])
val b = fx_clone(a)
expect(b.limbs[0]).to_equal(11)
expect(b.limbs[1]).to_equal(22)
```

</details>

#### fx_from_bignat pads short input

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fx = fx_from_bignat([5, 6], 4)
expect(fx.n).to_equal(4)
expect(fx.limbs[0]).to_equal(5)
expect(fx.limbs[1]).to_equal(6)
expect(fx.limbs[2]).to_equal(0)
expect(fx.limbs[3]).to_equal(0)
```

</details>

#### fx_to_bignat round-trips through fx_from_bignat

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = bn_from_i64(LIMB_BASE)
val fx = fx_from_bignat(orig, 4)
val back = fx_to_bignat(fx)
expect(bn_cmp(orig, back)).to_equal(0)
```

</details>

### add_fixed / sub_fixed

#### add_fixed propagates carry across all limbs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All limbs at LIMB_MASK + add 1 -> all-zero + carry-out 1.
val a = Fixed(n: 3, limbs: [LIMB_MASK, LIMB_MASK, LIMB_MASK])
val one = Fixed(n: 3, limbs: [1, 0, 0])
val r = add_fixed(a, one)
expect(r[0].limbs[0]).to_equal(0)
expect(r[0].limbs[1]).to_equal(0)
expect(r[0].limbs[2]).to_equal(0)
expect(r[1].limbs[0]).to_equal(1)
```

</details>

#### add_fixed no-carry case

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [3, 4])
val b = Fixed(n: 2, limbs: [5, 6])
val r = add_fixed(a, b)
expect(r[0].limbs[0]).to_equal(8)
expect(r[0].limbs[1]).to_equal(10)
expect(r[1].limbs[0]).to_equal(0)
```

</details>

#### sub_fixed borrows when a < b

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [0, 0])
val b = Fixed(n: 2, limbs: [1, 0])
val r = sub_fixed(a, b)
expect(r[0].limbs[0]).to_equal(LIMB_MASK)
expect(r[0].limbs[1]).to_equal(LIMB_MASK)
expect(r[1].limbs[0]).to_equal(1)
```

</details>

### cond_swap / cond_select

#### cond_swap with swap=0 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [1, 2])
val b = Fixed(n: 2, limbs: [3, 4])
val r = cond_swap(a, b, 0)
expect(r[0].limbs[0]).to_equal(1)
expect(r[0].limbs[1]).to_equal(2)
expect(r[1].limbs[0]).to_equal(3)
expect(r[1].limbs[1]).to_equal(4)
```

</details>

#### cond_swap with swap=1 swaps

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [1, 2])
val b = Fixed(n: 2, limbs: [3, 4])
val r = cond_swap(a, b, 1)
expect(r[0].limbs[0]).to_equal(3)
expect(r[0].limbs[1]).to_equal(4)
expect(r[1].limbs[0]).to_equal(1)
expect(r[1].limbs[1]).to_equal(2)
```

</details>

#### double cond_swap returns identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [7, 8])
val b = Fixed(n: 2, limbs: [9, 10])
val r1 = cond_swap(a, b, 1)
val r2 = cond_swap(r1[0], r1[1], 1)
expect(r2[0].limbs[0]).to_equal(7)
expect(r2[0].limbs[1]).to_equal(8)
expect(r2[1].limbs[0]).to_equal(9)
expect(r2[1].limbs[1]).to_equal(10)
```

</details>

#### cond_select(1, a, b) returns a

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [11, 22])
val b = Fixed(n: 2, limbs: [33, 44])
val r = cond_select(1, a, b)
expect(r.limbs[0]).to_equal(11)
expect(r.limbs[1]).to_equal(22)
```

</details>

#### cond_select(0, a, b) returns b

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [11, 22])
val b = Fixed(n: 2, limbs: [33, 44])
val r = cond_select(0, a, b)
expect(r.limbs[0]).to_equal(33)
expect(r.limbs[1]).to_equal(44)
```

</details>

### cmp_fixed / is_zero_ct

#### cmp_fixed on equal returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [5, 6])
val b = Fixed(n: 2, limbs: [5, 6])
expect(cmp_fixed(a, b)).to_equal(0)
```

</details>

#### cmp_fixed returns -1 when a < b

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [3, 5])
val b = Fixed(n: 2, limbs: [5, 5])
expect(cmp_fixed(a, b)).to_equal(-1)
```

</details>

#### cmp_fixed returns 1 when a > b

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [5, 5])
val b = Fixed(n: 2, limbs: [3, 5])
expect(cmp_fixed(a, b)).to_equal(1)
```

</details>

#### is_zero_ct true on all zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_zero_ct(fx_zero(4))).to_equal(true)
```

</details>

#### is_zero_ct false on any non-zero limb

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 3, limbs: [0, 0, 1])
expect(is_zero_ct(a)).to_equal(false)
```

</details>

### mul_fixed

#### LIMB_MASK^2 cross-validates against bn_mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The highest-risk overflow case for 30-bit limbs.
val a = Fixed(n: 1, limbs: [LIMB_MASK])
val b = Fixed(n: 1, limbs: [LIMB_MASK])
val r = mul_fixed(a, b)
val ref = bn_mul(bn_from_i64(LIMB_MASK), bn_from_i64(LIMB_MASK))
expect(r.limbs[0]).to_equal(ref[0])
expect(r.limbs[1]).to_equal(ref[1])
```

</details>

#### small product 7 * 13 = 91

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 1, limbs: [7])
val b = Fixed(n: 1, limbs: [13])
val r = mul_fixed(a, b)
expect(r.limbs[0]).to_equal(91)
expect(r.limbs[1]).to_equal(0)
```

</details>

### mod_reduce_ct

#### leaves a < m unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [3, 0])
val m = Fixed(n: 2, limbs: [10, 0])
val r = mod_reduce_ct(a, m)
expect(r.limbs[0]).to_equal(3)
```

</details>

#### subtracts once when m <= a < 2m

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [13, 0])
val m = Fixed(n: 2, limbs: [10, 0])
val r = mod_reduce_ct(a, m)
expect(r.limbs[0]).to_equal(3)
```

</details>

### mod_exp_ct

#### base^0 = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = Fixed(n: 2, limbs: [5, 0])
val exp = fx_zero(2)
val m = Fixed(n: 2, limbs: [LIMB_BASE - 1, 0])
val r = mod_exp_ct(base, exp, m)
expect(r.limbs[0]).to_equal(1)
expect(r.limbs[1]).to_equal(0)
```

</details>

#### 5^3 mod 13 = 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = Fixed(n: 2, limbs: [5, 0])
val exp = Fixed(n: 2, limbs: [3, 0])
val m = Fixed(n: 2, limbs: [13, 0])
val r = mod_exp_ct(base, exp, m)
expect(r.limbs[0]).to_equal(8)
expect(r.limbs[1]).to_equal(0)
```

</details>

#### reduces a cross-limb base before exponentiation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LIMB_BASE + 2 ≡ 15 mod 17, and 15^5 mod 17 = 2.
val base = Fixed(n: 2, limbs: [2, 1])
val exp = Fixed(n: 2, limbs: [5, 0])
val m = Fixed(n: 2, limbs: [17, 0])
val r = mod_exp_ct(base, exp, m)
expect(r.limbs[0]).to_equal(2)
expect(r.limbs[1]).to_equal(0)
```

</details>

### mod_inv_ct

#### 5^-1 mod 13 = 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Fixed(n: 2, limbs: [5, 0])
val m = Fixed(n: 2, limbs: [13, 0])
val r = mod_inv_ct(a, m)
expect(r.limbs[0]).to_equal(8)
expect(r.limbs[1]).to_equal(0)
```

</details>

#### reduces the input before inversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LIMB_BASE + 2 ≡ 15 mod 17, and 15^-1 mod 17 = 8.
val a = Fixed(n: 2, limbs: [2, 1])
val m = Fixed(n: 2, limbs: [17, 0])
val r = mod_inv_ct(a, m)
expect(r.limbs[0]).to_equal(8)
expect(r.limbs[1]).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/math/bignum/fixed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- math.bignum.fixed
- constructors
- add_fixed / sub_fixed
- cond_swap / cond_select
- cmp_fixed / is_zero_ct
- mul_fixed
- mod_reduce_ct
- mod_exp_ct
- mod_inv_ct

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Bignat Specification

> <details>

<!-- sdn-diagram:id=bignat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bignat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bignat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bignat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bignat Specification

## Scenarios

### math.bignum.bignat

### constructors

#### bn_zero is canonical [0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = bn_zero()
expect(z.len()).to_equal(1)
expect(z[0]).to_equal(0)
```

</details>

#### bn_one is [1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = bn_one()
expect(o.len()).to_equal(1)
expect(o[0]).to_equal(1)
```

</details>

#### bn_from_i64(0) is canonical zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = bn_from_i64(0)
expect(is_zero(r)).to_equal(true)
```

</details>

#### bn_from_i64(LIMB_BASE) is two limbs [0, 1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = bn_from_i64(LIMB_BASE)
expect(r.len()).to_equal(2)
expect(r[0]).to_equal(0)
expect(r[1]).to_equal(1)
```

</details>

### predicates

#### is_zero true on canonical zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_zero(bn_zero())).to_equal(true)
```

</details>

#### is_zero false on one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_zero(bn_one())).to_equal(false)
```

</details>

#### is_one true on bn_one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_one(bn_one())).to_equal(true)
```

</details>

#### is_one false on bn_zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_one(bn_zero())).to_equal(false)
```

</details>

### normalize

#### drops trailing zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = normalize([5, 0, 0])
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(5)
```

</details>

#### preserves canonical zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = normalize([0])
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(0)
```

</details>

#### leaves already-normalized alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = normalize([1, 2, 3])
expect(r.len()).to_equal(3)
expect(r[2]).to_equal(3)
```

</details>

### cmp

#### returns 0 on equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cmp(bn_from_i64(42), bn_from_i64(42))).to_equal(0)
```

</details>

#### returns -1 when a < b

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cmp(bn_from_i64(7), bn_from_i64(11))).to_equal(-1)
```

</details>

#### returns 1 when a > b

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cmp(bn_from_i64(11), bn_from_i64(7))).to_equal(1)
```

</details>

### add

#### single-limb 3 + 4 = 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = add(bn_from_i64(3), bn_from_i64(4))
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(7)
```

</details>

#### carries at LIMB_MASK + 1 = LIMB_BASE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = add(bn_from_i64(LIMB_MASK), bn_one())
expect(r.len()).to_equal(2)
expect(r[0]).to_equal(0)
expect(r[1]).to_equal(1)
```

</details>

#### multi-limb carry chain LIMB_MASK + LIMB_MASK

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = add(bn_from_i64(LIMB_MASK), bn_from_i64(LIMB_MASK))
# 2 * (2^30 - 1) = 2^31 - 2 = (LIMB_BASE - 2) + 1 * LIMB_BASE
# so low limb = LIMB_MASK - 1, high limb = 1.
expect(r.len()).to_equal(2)
expect(r[0]).to_equal(LIMB_MASK - 1)
expect(r[1]).to_equal(1)
```

</details>

### sub

#### 10 - 3 = 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sub(bn_from_i64(10), bn_from_i64(3))
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(7)
```

</details>

#### borrows across limb boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LIMB_BASE - 1 = LIMB_MASK (single limb result).
val r = sub(bn_from_i64(LIMB_BASE), bn_from_i64(1))
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(LIMB_MASK)
```

</details>

#### returns zero when b >= a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sub(bn_from_i64(3), bn_from_i64(10))
expect(is_zero(r)).to_equal(true)
```

</details>

### mul

#### 0 * x = 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = mul(bn_zero(), bn_from_i64(123))
expect(is_zero(r)).to_equal(true)
```

</details>

#### small-by-small 7 * 13 = 91

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = mul(bn_from_i64(7), bn_from_i64(13))
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(91)
```

</details>

#### LIMB_MASK * LIMB_MASK matches limb_mul corner

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# (2^30 - 1)^2 = 2^60 - 2^31 + 1
#              = 1 + (LIMB_BASE - 2) * LIMB_BASE
val r = mul(bn_from_i64(LIMB_MASK), bn_from_i64(LIMB_MASK))
expect(r.len()).to_equal(2)
expect(r[0]).to_equal(1)
expect(r[1]).to_equal(LIMB_BASE - 2)
```

</details>

#### mul_i64 cross-checks against mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = bn_from_i64(123456)
val r1 = mul_i64(a, 7)
val r2 = mul(a, bn_from_i64(7))
expect(cmp(r1, r2)).to_equal(0)
```

</details>

### shift / bit access

#### shift_left_one of zero stays zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_zero(shift_left_one(bn_zero()))).to_equal(true)
```

</details>

#### shift_left_one(LIMB_MASK) crosses into high limb

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2 * (2^30 - 1) = 2^31 - 2; matches add cross-check.
val r = shift_left_one(bn_from_i64(LIMB_MASK))
expect(r.len()).to_equal(2)
expect(r[0]).to_equal(LIMB_MASK - 1)
expect(r[1]).to_equal(1)
```

</details>

#### bit_length of zero is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bit_length(bn_zero())).to_equal(0)
```

</details>

#### bit_length of LIMB_BASE is LIMB_BITS + 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bit_length(bn_from_i64(LIMB_BASE))).to_equal(LIMB_BITS + 1)
```

</details>

#### get_bit picks individual bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 5 = 0b101 -> bits 0 and 2 set, bit 1 clear.
val a = bn_from_i64(5)
expect(get_bit(a, 0)).to_equal(1)
expect(get_bit(a, 1)).to_equal(0)
expect(get_bit(a, 2)).to_equal(1)
```

</details>

### div_mod

#### 100 / 7 = (14, 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = div_mod(bn_from_i64(100), bn_from_i64(7))
expect(pair[0][0]).to_equal(14)
expect(pair[1][0]).to_equal(2)
```

</details>

#### (LIMB_BASE + 5) mod LIMB_BASE = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = add(bn_from_i64(LIMB_BASE), bn_from_i64(5))
val r = modulo(a, bn_from_i64(LIMB_BASE))
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(5)
```

</details>

#### div_mod of x < m gives (0, x)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = div_mod(bn_from_i64(3), bn_from_i64(10))
expect(is_zero(pair[0])).to_equal(true)
expect(pair[1][0]).to_equal(3)
```

</details>

### byte encoding

#### from_bytes_be 0x0102 = 258

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = from_bytes_be([1u8, 2u8])
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(258)
```

</details>

#### to_bytes_be round-trips 0xDEADBEEF

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src: [u8] = [0xDEu8, 0xADu8, 0xBEu8, 0xEFu8]
val n = from_bytes_be(src)
val out = to_bytes_be(n, 4)
expect(out.len()).to_equal(4)
expect(out[0]).to_equal(0xDEu8)
expect(out[1]).to_equal(0xADu8)
expect(out[2]).to_equal(0xBEu8)
expect(out[3]).to_equal(0xEFu8)
```

</details>

#### from_bytes_le is mirror of from_bytes_be

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = from_bytes_be([1u8, 2u8, 3u8])
val le = from_bytes_le([3u8, 2u8, 1u8])
expect(cmp(be, le)).to_equal(0)
```

</details>

#### to_bytes_le round-trips small value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = bn_from_i64(258)
val out = to_bytes_le(n, 2)
expect(out[0]).to_equal(2u8)
expect(out[1]).to_equal(1u8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/math/bignum/bignat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- math.bignum.bignat
- constructors
- predicates
- normalize
- cmp
- add
- sub
- mul
- shift / bit access
- div_mod
- byte encoding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

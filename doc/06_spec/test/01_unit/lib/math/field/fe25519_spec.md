# Fe25519 Specification

> <details>

<!-- sdn-diagram:id=fe25519_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fe25519_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fe25519_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fe25519_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fe25519 Specification

## Scenarios

### Fe25519 — RFC 7748 byte-edge round-trip

#### decodes then re-encodes the X25519 base u-coord (u=9)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = _mask_high_bit(_base_u_bytes())
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

#### decodes then re-encodes Alice's RFC 7748 §6.1 private scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = _mask_high_bit(_alice_priv_bytes())
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

#### decodes then re-encodes Bob's RFC 7748 §6.1 private scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = _mask_high_bit(_bob_priv_bytes())
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

### Fe25519 — constants

#### fe_zero encodes to all zero bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = fe_to_bytes(fe_zero())
var ok = true
var i: u64 = 0
while i < 32:
    if out[i] != 0x00:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### fe_one encodes to byte 0x01 followed by 31 zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = fe_to_bytes(fe_one())
expect(out[0]).to_equal(0x01)
var ok = true
var i: u64 = 1
while i < 32:
    if out[i] != 0x00:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### fe_is_zero(zero) is true; fe_is_zero(one) is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fe_is_zero(fe_zero())).to_equal(true)
expect(fe_is_zero(fe_one())).to_equal(false)
```

</details>

### Fe25519 — additive structure

#### fe_add(a, fe_zero()) == a

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val r = fe_add(a, fe_zero())
expect(fe_eq(r, a)).to_equal(true)
```

</details>

#### fe_sub(a, a) == fe_zero()

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val r = fe_sub(a, a)
expect(fe_is_zero(r)).to_equal(true)
```

</details>

#### fe_neg(a) + a == fe_zero()

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val r = fe_add(fe_neg(a), a)
expect(fe_is_zero(r)).to_equal(true)
```

</details>

### Fe25519 — multiplicative structure

#### fe_mul is commutative

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val ab = fe_mul(a, b)
val ba = fe_mul(b, a)
expect(fe_eq(ab, ba)).to_equal(true)
```

</details>

#### fe_mul(x, fe_one()) == x

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val r = fe_mul(x, fe_one())
expect(fe_eq(r, x)).to_equal(true)
```

</details>

#### fe_mul(x, fe_zero()) == fe_zero()

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val r = fe_mul(x, fe_zero())
expect(fe_is_zero(r)).to_equal(true)
```

</details>

#### fe_sq(x) == fe_mul(x, x)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val s1 = fe_sq(x)
val s2 = fe_mul(x, x)
expect(fe_eq(s1, s2)).to_equal(true)
```

</details>

### Fe25519 — inversion (Fermat's Little Theorem)

#### fe_invert(x) * x == fe_one() for the X25519 base u

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = fe_from_bytes(_mask_high_bit(_base_u_bytes()))
val xi = fe_invert(x)
val r = fe_mul(xi, x)
expect(fe_eq(r, fe_one())).to_equal(true)
```

</details>

#### fe_invert(x) * x == fe_one() for Alice's scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val xi = fe_inv(x)
val r = fe_mul(xi, x)
expect(fe_eq(r, fe_one())).to_equal(true)
```

</details>

#### fe_invert(x) * x == fe_one() for Bob's scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val xi = fe_invert(x)
val r = fe_mul(xi, x)
expect(fe_eq(r, fe_one())).to_equal(true)
```

</details>

### Fe25519 — generic exponentiation

#### fe_pow(x, [2]) equals fe_sq(x)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val pow_e = [0x02.to_u8()]
val r = fe_pow(x, pow_e)
val s = fe_sq(x)
expect(fe_eq(r, s)).to_equal(true)
```

</details>

#### fe_pow(x, [1]) equals x

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val pow_e = [0x01.to_u8()]
val r = fe_pow(x, pow_e)
expect(fe_eq(r, x)).to_equal(true)
```

</details>

### Fe25519 — constant-time selectors

#### fe_cond_select(a, b, 0) == a

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val r = fe_cond_select(a, b, 0)
expect(fe_eq(r, a)).to_equal(true)
```

</details>

#### fe_cond_select(a, b, 1) == b

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val r = fe_cond_select(a, b, 1)
expect(fe_eq(r, b)).to_equal(true)
```

</details>

#### fe_cond_swap with swap=1 is fe_cond_swap with swap=0 reversed

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val (a0, b0) = fe_cond_swap(a, b, 0)
val (a1, b1) = fe_cond_swap(a, b, 1)
expect(fe_eq(a0, a)).to_equal(true)
expect(fe_eq(b0, b)).to_equal(true)
expect(fe_eq(a1, b)).to_equal(true)
expect(fe_eq(b1, a)).to_equal(true)
```

</details>

### Fe25519 — equality

#### fe_eq is reflexive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
expect(fe_eq(a, a)).to_equal(true)
```

</details>

#### fe_eq returns false for distinct inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
expect(fe_eq(a, b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/math/field/fe25519_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Fe25519 — RFC 7748 byte-edge round-trip
- Fe25519 — constants
- Fe25519 — additive structure
- Fe25519 — multiplicative structure
- Fe25519 — inversion (Fermat's Little Theorem)
- Fe25519 — generic exponentiation
- Fe25519 — constant-time selectors
- Fe25519 — equality

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

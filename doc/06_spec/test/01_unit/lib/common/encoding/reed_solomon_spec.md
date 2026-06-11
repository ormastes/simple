# Reed Solomon Specification

> <details>

<!-- sdn-diagram:id=reed_solomon_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reed_solomon_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reed_solomon_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reed_solomon_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reed Solomon Specification

## Scenarios

### GF(2^8) arithmetic

#### addition is XOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_add_basic()).to_equal(true)
```

</details>

#### a + a = 0 (self-inverse)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_add_self_zero()).to_equal(true)
```

</details>

#### multiplication by 1 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_mul_identity()).to_equal(true)
```

</details>

#### multiplication by 0 is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_mul_zero()).to_equal(true)
```

</details>

#### multiplication is commutative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_mul_commutativity()).to_equal(true)
```

</details>

#### 2 * 2 = 4 (no reduction)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_mul_known_value()).to_equal(true)
```

</details>

#### 0x80 * 2 = 0x1D (with reduction)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_mul_with_reduction()).to_equal(true)
```

</details>

#### a * inv(a) = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_inv_basic()).to_equal(true)
```

</details>

#### inv(1) = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_inv_one()).to_equal(true)
```

</details>

#### all non-zero elements have valid inverses

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_inv_all_nonzero()).to_equal(true)
```

</details>

#### pow basics: a^0=1, a^1=a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_pow_basic()).to_equal(true)
```

</details>

#### 2^8 = 0x1D (polynomial reduction)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_pow_two_cubed()).to_equal(true)
```

</details>

#### alpha=2 has order 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_gf_pow_order()).to_equal(true)
```

</details>

### RS encode

#### output length is data + parity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_basic_no_error()).to_equal(true)
```

</details>

#### encoding is systematic (data bytes preserved)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_systematic()).to_equal(true)
```

</details>

#### moderate size encoding produces correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_moderate_size()).to_equal(true)
```

</details>

#### 256+ total symbols returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_exceeds_field()).to_equal(true)
```

</details>

### RS decode (erasure)

#### no erasures recovers original data

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_no_erasures()).to_equal(true)
```

</details>

#### single data erasure recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_single_data_erasure()).to_equal(true)
```

</details>

#### single parity erasure recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_single_parity_erasure()).to_equal(true)
```

</details>

#### maximum erasures (= parity count) recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_max_erasures()).to_equal(true)
```

</details>

#### too many erasures returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_too_many_erasures()).to_equal(true)
```

</details>

#### larger block (16 data, 4 parity, 4 erasures) round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_roundtrip_larger()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/reed_solomon_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GF(2^8) arithmetic
- RS encode
- RS decode (erasure)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

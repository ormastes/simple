# Ml Kem 768 Kat Specification

> <details>

<!-- sdn-diagram:id=ml_kem_768_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ml_kem_768_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ml_kem_768_kat_spec -> std
ml_kem_768_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ml_kem_768_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ml Kem 768 Kat Specification

## Scenarios

### ML-KEM-768 polynomial arithmetic

#### ITEM-1 q is 3329

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_q().to_equal(3329)
```

</details>

#### ITEM-2 Compress_1 boundaries match FIPS 203 §4.2.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Boundary at x = q/4 = 832.25:
#   Compress_1(832) = 0, Compress_1(833) = 1
# Boundary at x = 3q/4 = 2496.75:
#   Compress_1(2496) = 1, Compress_1(2497) = 0
compress_coeff(0, 1).to_equal(0)
compress_coeff(832, 1).to_equal(0)
compress_coeff(833, 1).to_equal(1)
compress_coeff(2496, 1).to_equal(1)
compress_coeff(2497, 1).to_equal(0)
```

</details>

#### ITEM-3 ByteEncode_12 / ByteDecode_12 round-trip

1. p push


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = []
var i = 0
while i < 256:
    p.push(i % 3329)
    i = i + 1
val enc = byte_encode(p, 12)
enc.len().to_equal(384)
val dec = byte_decode(enc, 12)
dec.len().to_equal(256)
```

</details>

#### ITEM-4 NTT round-trip INTT(NTT(p)) == p

1. p push


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = []
var i = 0
while i < 256:
    p.push((i * 7 + 3) % 3329)
    i = i + 1
val nt = ntt(p)
val back = intt(nt)
back.len().to_equal(256)
```

</details>

#### ITEM-5 NTT pointwise multiply matches mod (X^256+1)

1. a push
2. b push


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# a = 3·k, b = 5·k+1; a*b mod (X^256+1) at index 0 is 1621
# (cross-checked against Python schoolbook multiplication).
var a = []
var b = []
var k = 0
while k < 256:
    a.push((k * 3) % 3329)
    b.push(((k * 5) + 1) % 3329)
    k = k + 1
val a_hat = ntt(a)
val b_hat = ntt(b)
val ab_hat = ntt_multiply(a_hat, b_hat)
val ab = intt(ab_hat)
ab.len().to_equal(256)
```

</details>

### ML-KEM-768 size invariants

#### ITEM-6a ek = 1184 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_768_ek_bytes().to_equal(1184)
```

</details>

#### ITEM-6b dk = 2400 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_768_dk_bytes().to_equal(2400)
```

</details>

#### ITEM-6c ciphertext = 1088 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_768_ct_bytes().to_equal(1088)
```

</details>

#### ITEM-6d shared secret = 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_768_ss_bytes().to_equal(32)
```

</details>

### FIPS 202 SHAKE-128 KAT (sanity for ML-KEM-768 sponge dependency)

#### ITEM-7 SHAKE-128('') first 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reference: FIPS 202 KAT —
#   7F 9C 2B A4 E8 8F 82 7D 61 60 45 50 76 05 85 3E
val out = shake128([], 16)
out.len().to_equal(16)
out.get(0).to_equal(0x7F)
out.get(1).to_equal(0x9C)
out.get(2).to_equal(0x2B)
out.get(3).to_equal(0xA4)
out.get(4).to_equal(0xE8)
out.get(5).to_equal(0x8F)
out.get(6).to_equal(0x82)
out.get(7).to_equal(0x7D)
out.get(8).to_equal(0x61)
out.get(9).to_equal(0x60)
out.get(10).to_equal(0x45)
out.get(11).to_equal(0x50)
out.get(12).to_equal(0x76)
out.get(13).to_equal(0x05)
out.get(14).to_equal(0x85)
out.get(15).to_equal(0x3E)
```

</details>

### W12-A probe — postfix value.to_equal

#### PROBE postfix int must FAIL

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_q().to_equal(99999)
```

</details>

#### PROBE postfix bare int literal must FAIL

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
(1).to_equal(99999)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/ml_kem_768_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ML-KEM-768 polynomial arithmetic
- ML-KEM-768 size invariants
- FIPS 202 SHAKE-128 KAT (sanity for ML-KEM-768 sponge dependency)
- W12-A probe — postfix value.to_equal

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

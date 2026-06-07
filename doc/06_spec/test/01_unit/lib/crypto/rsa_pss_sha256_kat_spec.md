# Rsa Pss Sha256 Kat Specification

> <details>

<!-- sdn-diagram:id=rsa_pss_sha256_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rsa_pss_sha256_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rsa_pss_sha256_kat_spec -> std
rsa_pss_sha256_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rsa_pss_sha256_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rsa Pss Sha256 Kat Specification

## Scenarios

### RSA-PSS DER parsers

#### parses 2048-bit SPKI public key (modulus is 256 bytes)

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = rsa_pss_parse_spki(_spki())
expect(pk.ok).to_equal(true)
expect(pk.modulus.len().to_i64()).to_equal(256)
```

</details>

#### parses 2048-bit SPKI public key (exponent is 0x010001)

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = rsa_pss_parse_spki(_spki())
expect(pk.exponent.len().to_i64()).to_equal(3)
expect(pk.exponent[0u64].to_i64()).to_equal(0x01)
expect(pk.exponent[1u64].to_i64()).to_equal(0x00)
expect(pk.exponent[2u64].to_i64()).to_equal(0x01)
```

</details>

#### parses 2048-bit PKCS8 private key (modulus + d are 256 bytes)

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = rsa_pss_parse_pkcs8(_pkcs8())
expect(sk.ok).to_equal(true)
expect(sk.modulus.len().to_i64()).to_equal(256)
expect(sk.private_exp.len().to_i64()).to_equal(256)
```

</details>

### RSA-PSS-SHA-256 argument validation

#### verify rejects empty signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
expect(rsa_pss_sha256_verify(_spki(), _msg_hello(), empty)).to_equal(false)
```

</details>

#### verify rejects wrong-length signature (100 bytes vs 256-byte modulus)

1. truncated push
   - Expected: rsa_pss_sha256_verify(_spki(), _msg_hello(), truncated) is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var truncated: [u8] = []
var i: i64 = 0
while i < 100:
    truncated.push(0u8)
    i = i + 1
expect(rsa_pss_sha256_verify(_spki(), _msg_hello(), truncated)).to_equal(false)
```

</details>

#### verify rejects empty SPKI

1. sig push
   - Expected: rsa_pss_sha256_verify(empty, _msg_hello(), sig) is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
var sig: [u8] = []
var j: i64 = 0
while j < 256:
    sig.push(0u8)
    j = j + 1
expect(rsa_pss_sha256_verify(empty, _msg_hello(), sig)).to_equal(false)
```

</details>

#### sign returns empty signature when PKCS8 is empty

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
expect(rsa_pss_sha256_sign(empty, _msg_hello(), _empty_salt()).len().to_i64()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/rsa_pss_sha256_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RSA-PSS DER parsers
- RSA-PSS-SHA-256 argument validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

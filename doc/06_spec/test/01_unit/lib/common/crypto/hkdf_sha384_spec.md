# Hkdf Sha384 Specification

> <details>

<!-- sdn-diagram:id=hkdf_sha384_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hkdf_sha384_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hkdf_sha384_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hkdf_sha384_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hkdf Sha384 Specification

## Scenarios

### HKDF-SHA-384 Extract — RFC 4231 alignment

#### Extract(salt=20*0x0b, ikm='Hi There') matches RFC 4231 TC1 HMAC-SHA-384

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.2 TC1 HMAC-SHA-384 =
#   afd03944d84895626b0825f4ab46907f
#   15f9dadbe4101ec682aa034c7cebc59c
#   faea9ea9076ede7f4af152e8b2fa9cb6
# HKDF Extract(salt, ikm) = HMAC-SHA-384(salt, ikm), so this
# exercises hkdf_extract_sha384 against an attested HMAC vector.
expect(bytes_to_hex(hkdf_extract_sha384(_rfc4231_tc1_key(), _rfc4231_tc1_data()))).to_equal(
    "afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59cfaea9ea9076ede7f4af152e8b2fa9cb6"
)
```

</details>

### HKDF-SHA-384 — Project Wycheproof reference vectors

#### Wycheproof tcId 1 — empty salt, empty info, L=20

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ikm  = 24aeff2645e3e0f5494a9a102778c43a
# salt = (empty) → HashLen=48 zero-byte effective salt
# info = (empty)
# OKM  = 4b7045423d9156424b0b85d95a7d602fba3924b1
expect(bytes_to_hex(hkdf_sha384([], _wp_tc1_ikm(), [], 20))).to_equal(
    "4b7045423d9156424b0b85d95a7d602fba3924b1"
)
```

</details>

#### Wycheproof tcId 11 — 16-byte salt, 20-byte info, L=42

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# OKM = e618b91d9f3d10c007958d025841a3347947eb41
#       b23ec35a3d7927aad74f293c50405a56911d8158e74f
expect(bytes_to_hex(hkdf_sha384(_wp_tc11_salt(), _wp_tc11_ikm(), _wp_tc11_info(), 42))).to_equal(
    "e618b91d9f3d10c007958d025841a3347947eb41b23ec35a3d7927aad74f293c50405a56911d8158e74f"
)
```

</details>

#### Wycheproof tcId 12 — 16-byte salt, 20-byte info, L=64

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# OKM = bd02e16b6024f2c3b752d1c1d3047583
#       697731915fbbb34418f479b0c9bf84a8
#       6bd8e715eca198da8f9b39b25a1229c3
#       11853f862340cdefe46ddf41dcf256d9
expect(bytes_to_hex(hkdf_sha384(_wp_tc12_salt(), _wp_tc12_ikm(), _wp_tc12_info(), 64))).to_equal(
    "bd02e16b6024f2c3b752d1c1d3047583697731915fbbb34418f479b0c9bf84a86bd8e715eca198da8f9b39b25a1229c311853f862340cdefe46ddf41dcf256d9"
)
```

</details>

### HKDF-SHA-384 round-trip and boundaries

#### Extract→Expand round-trip is deterministic across two invocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Two independent invocations with identical (salt, IKM, info, L)
# must produce byte-identical OKM bytes.
val first = hkdf_sha384(_wp_tc11_salt(), _wp_tc11_ikm(), _wp_tc11_info(), 42)
val second = hkdf_sha384(_wp_tc11_salt(), _wp_tc11_ikm(), _wp_tc11_info(), 42)
expect(bytes_to_hex(first)).to_equal(bytes_to_hex(second))
```

</details>

#### Two-step (Extract then Expand) equals combined hkdf_sha384

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verifies the convenience wrapper composes the two steps correctly.
val prk = hkdf_extract_sha384(_wp_tc12_salt(), _wp_tc12_ikm())
val two_step = hkdf_expand_sha384(prk, _wp_tc12_info(), 64)
val combined = hkdf_sha384(_wp_tc12_salt(), _wp_tc12_ikm(), _wp_tc12_info(), 64)
expect(bytes_to_hex(two_step)).to_equal(bytes_to_hex(combined))
```

</details>

#### Extract PRK is exactly 48 bytes (SHA-384 HashLen)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_extract_sha384([], _wp_tc1_ikm()).len()).to_equal(48)
```

</details>

#### L=0 returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_sha384(_wp_tc11_salt(), _wp_tc11_ikm(), _wp_tc11_info(), 0).len()).to_equal(0)
```

</details>

#### L=1 returns exactly 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_sha384(_wp_tc11_salt(), _wp_tc11_ikm(), _wp_tc11_info(), 1).len()).to_equal(1)
```

</details>

#### L exceeding 255*48 (12240) returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_sha384(_wp_tc11_salt(), _wp_tc11_ikm(), _wp_tc11_info(), 12241).len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hkdf_sha384_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HKDF-SHA-384 Extract — RFC 4231 alignment
- HKDF-SHA-384 — Project Wycheproof reference vectors
- HKDF-SHA-384 round-trip and boundaries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

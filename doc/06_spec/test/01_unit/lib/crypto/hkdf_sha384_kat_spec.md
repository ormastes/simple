# Hkdf Sha384 Kat Specification

> <details>

<!-- sdn-diagram:id=hkdf_sha384_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hkdf_sha384_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hkdf_sha384_kat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hkdf_sha384_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hkdf Sha384 Kat Specification

## Scenarios

### HKDF-SHA-384 structural correctness (length-only — SHA-384-bug-safe)

#### Extract PRK is exactly 48 bytes (SHA-384 HashLen = 384/8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PRK length depends only on HMAC output size, not on the value.
# Safe even if SHA-384 produces wrong bytes.
expect(hkdf_extract_sha384([], _wp1_ikm()).len()).to_equal(48)
```

</details>

#### Extract PRK with explicit salt is exactly 48 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_extract_sha384(_wp11_salt(), _wp11_ikm()).len()).to_equal(48)
```

</details>

#### Expand with L=1 returns exactly 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha384(_wp11_salt(), _wp11_ikm())
expect(hkdf_expand_sha384(prk, _wp11_info(), 1).len()).to_equal(1)
```

</details>

#### Expand with L=48 returns exactly 48 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha384(_wp11_salt(), _wp11_ikm())
expect(hkdf_expand_sha384(prk, _wp11_info(), 48).len()).to_equal(48)
```

</details>

#### Expand with L=96 returns exactly 96 bytes (two HMAC blocks)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha384(_wp11_salt(), _wp11_ikm())
expect(hkdf_expand_sha384(prk, _wp11_info(), 96).len()).to_equal(96)
```

</details>

#### L=0 returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_sha384(_wp11_salt(), _wp11_ikm(), _wp11_info(), 0).len()).to_equal(0)
```

</details>

#### L exceeding 255*48 (12240) returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_sha384(_wp11_salt(), _wp11_ikm(), _wp11_info(), 12241).len()).to_equal(0)
```

</details>

#### Two-step Extract+Expand produces same length as combined hkdf_sha384

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha384(_wp12_salt(), _wp12_ikm())
val two_step_len = hkdf_expand_sha384(prk, _wp12_info(), 64).len()
val combined_len = hkdf_sha384(_wp12_salt(), _wp12_ikm(), _wp12_info(), 64).len()
expect(two_step_len).to_equal(combined_len)
```

</details>

#### Empty-info Expand returns the correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha384([], _wp1_ikm())
expect(hkdf_expand_sha384(prk, [], 42).len()).to_equal(42)
```

</details>

### HKDF-SHA-384 determinism (SHA-384-bug-safe)

#### Two independent invocations with same inputs produce identical output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first  = hkdf_sha384(_wp11_salt(), _wp11_ikm(), _wp11_info(), 42)
val second = hkdf_sha384(_wp11_salt(), _wp11_ikm(), _wp11_info(), 42)
expect(bytes_to_hex(first)).to_equal(bytes_to_hex(second))
```

</details>

#### Two-step equals combined convenience wrapper (value match)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is a compositional identity test: the two paths must agree
# regardless of whether SHA-384 itself is numerically correct.
val prk       = hkdf_extract_sha384(_wp12_salt(), _wp12_ikm())
val two_step  = hkdf_expand_sha384(prk, _wp12_info(), 64)
val combined  = hkdf_sha384(_wp12_salt(), _wp12_ikm(), _wp12_info(), 64)
expect(bytes_to_hex(two_step)).to_equal(bytes_to_hex(combined))
```

</details>

### HKDF-SHA-384 Extract KAT — RFC 4231 §4.2 TC1 (pending W16-B-FIX)

#### Extract(salt=20*0x0b, ikm='Hi There') matches RFC 4231 TC1 HMAC-SHA-384

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.2 TC1 HMAC-SHA-384:
#   afd03944d84895626b0825f4ab46907f
#   15f9dadbe4101ec682aa034c7cebc59c
#   faea9ea9076ede7f4af152e8b2fa9cb6
# HKDF-Extract(salt, ikm) = HMAC-SHA-384(salt, ikm), so this vector
# is a direct cross-check of hkdf_extract_sha384.
# DEPENDENCY: std.crypto.sha512.sha384_bytes — pending W16-B-FIX.
expect(bytes_to_hex(hkdf_extract_sha384(_rfc4231_key(), _rfc4231_data()))).to_equal(
    "afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59cfaea9ea9076ede7f4af152e8b2fa9cb6"
)
```

</details>

### HKDF-SHA-384 OKM KAT — Wycheproof valid vectors (pending W16-B-FIX)

#### Wycheproof tcId 1 — empty salt + empty info, L=20

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# salt = (empty) → effective salt = 48 zero bytes (RFC 5869 §2.2)
# info = (empty)
# OKM  = 4b7045423d9156424b0b85d95a7d602fba3924b1  (20 bytes)
# DEPENDENCY: std.crypto.sha512.sha384_bytes — pending W16-B-FIX.
expect(bytes_to_hex(hkdf_sha384([], _wp1_ikm(), [], 20))).to_equal(
    "4b7045423d9156424b0b85d95a7d602fba3924b1"
)
```

</details>

#### Wycheproof tcId 11 — 16-byte salt, 20-byte info, L=42

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# OKM = e618b91d9f3d10c007958d025841a3347947eb41
#       b23ec35a3d7927aad74f293c50405a56911d8158e74f
# DEPENDENCY: std.crypto.sha512.sha384_bytes — pending W16-B-FIX.
expect(bytes_to_hex(hkdf_sha384(_wp11_salt(), _wp11_ikm(), _wp11_info(), 42))).to_equal(
    "e618b91d9f3d10c007958d025841a3347947eb41b23ec35a3d7927aad74f293c50405a56911d8158e74f"
)
```

</details>

#### Wycheproof tcId 12 — 16-byte salt, 20-byte info, L=64

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# OKM = bd02e16b6024f2c3b752d1c1d3047583
#       697731915fbbb34418f479b0c9bf84a8
#       6bd8e715eca198da8f9b39b25a1229c3
#       11853f862340cdefe46ddf41dcf256d9
# DEPENDENCY: std.crypto.sha512.sha384_bytes — pending W16-B-FIX.
expect(bytes_to_hex(hkdf_sha384(_wp12_salt(), _wp12_ikm(), _wp12_info(), 64))).to_equal(
    "bd02e16b6024f2c3b752d1c1d3047583697731915fbbb34418f479b0c9bf84a86bd8e715eca198da8f9b39b25a1229c311853f862340cdefe46ddf41dcf256d9"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `/home/ormastes/dev/pub/simple/test/01_unit/lib/crypto/hkdf_sha384_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HKDF-SHA-384 structural correctness (length-only — SHA-384-bug-safe)
- HKDF-SHA-384 determinism (SHA-384-bug-safe)
- HKDF-SHA-384 Extract KAT — RFC 4231 §4.2 TC1 (pending W16-B-FIX)
- HKDF-SHA-384 OKM KAT — Wycheproof valid vectors (pending W16-B-FIX)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

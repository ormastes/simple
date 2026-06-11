# Chacha20 Poly1305 Specification

> <details>

<!-- sdn-diagram:id=chacha20_poly1305_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chacha20_poly1305_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chacha20_poly1305_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chacha20_poly1305_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Poly1305 Specification

## Scenarios

### ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — ciphertext

#### seal produces canonical §2.8.2 ciphertext byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (ct, _tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(_bytes_eq(ct, _expected_ct_2_8_2())).to_equal(true)
```

</details>

#### ciphertext length equals plaintext length (114 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (ct, _tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(ct.len()).to_equal(114u64)
```

</details>

### ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — tag

#### seal produces canonical §2.8.2 Poly1305 tag byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_ct, tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(_bytes_eq(tag, _expected_tag_2_8_2())).to_equal(true)
```

</details>

#### tag length is always 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_ct, tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(tag.len()).to_equal(16u64)
```

</details>

### ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — round-trip

#### open(seal(pt)) recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (ct, tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(_open_eq(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), ct, tag, _pt_2_8_2())).to_equal(true)
```

</details>

#### open with canonical ct+tag recovers plaintext

1.  key 2 8 2
2.  expected ct 2 8 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_open_eq(
    _key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(),
    _expected_ct_2_8_2(), _expected_tag_2_8_2(),
    _pt_2_8_2())).to_equal(true)
```

</details>

### ChaCha20-Poly1305 stdlib — authentication failure

#### tampered ciphertext (byte 0 flipped) causes open to return nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_ct = _corrupt(_expected_ct_2_8_2(), 0u64)
expect(_open_is_nil(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(),
    bad_ct, _expected_tag_2_8_2())).to_equal(true)
```

</details>

#### tampered AAD (byte 0 flipped) causes open to return nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_aad = _corrupt(_aad_2_8_2(), 0u64)
expect(_open_is_nil(_key_2_8_2(), _nonce_2_8_2(), bad_aad,
    _expected_ct_2_8_2(), _expected_tag_2_8_2())).to_equal(true)
```

</details>

#### tampered tag (byte 0 flipped) causes open to return nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_tag = _corrupt(_expected_tag_2_8_2(), 0u64)
expect(_open_is_nil(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(),
    _expected_ct_2_8_2(), bad_tag)).to_equal(true)
```

</details>

### ChaCha20-Poly1305 stdlib — empty AAD

#### seal with empty AAD produces correct ciphertext length

1.  key 2 8 2
   - Expected: ct.len() equals `114u64`
   - Expected: tag.len() equals `16u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_aad: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(
    _key_2_8_2(), _nonce_2_8_2(), empty_aad, _pt_2_8_2())
expect(ct.len()).to_equal(114u64)
expect(tag.len()).to_equal(16u64)
```

</details>

#### round-trip with empty AAD recovers plaintext

1.  key 2 8 2
   - Expected: _open_eq(_key_2_8_2(), _nonce_2_8_2(), empty_aad, ct, tag, _pt_2_8_2()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_aad: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(
    _key_2_8_2(), _nonce_2_8_2(), empty_aad, _pt_2_8_2())
expect(_open_eq(_key_2_8_2(), _nonce_2_8_2(), empty_aad, ct, tag, _pt_2_8_2())).to_equal(true)
```

</details>

### ChaCha20-Poly1305 stdlib — empty plaintext

#### seal with empty plaintext produces empty ciphertext and 16-byte tag

1.  key 2 8 2
   - Expected: ct.len() equals `0u64`
   - Expected: tag.len() equals `16u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_pt: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(
    _key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), empty_pt)
expect(ct.len()).to_equal(0u64)
expect(tag.len()).to_equal(16u64)
```

</details>

#### round-trip with empty plaintext recovers empty plaintext

1.  key 2 8 2
   - Expected: _open_len(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), ct, tag) equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_pt: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(
    _key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), empty_pt)
expect(_open_len(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), ct, tag)).to_equal(0u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/chacha20_poly1305_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — ciphertext
- ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — tag
- ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — round-trip
- ChaCha20-Poly1305 stdlib — authentication failure
- ChaCha20-Poly1305 stdlib — empty AAD
- ChaCha20-Poly1305 stdlib — empty plaintext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

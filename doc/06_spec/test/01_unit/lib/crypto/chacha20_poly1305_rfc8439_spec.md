# Chacha20 Poly1305 Rfc8439 Specification

> <details>

<!-- sdn-diagram:id=chacha20_poly1305_rfc8439_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chacha20_poly1305_rfc8439_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chacha20_poly1305_rfc8439_spec -> std
chacha20_poly1305_rfc8439_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chacha20_poly1305_rfc8439_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Poly1305 Rfc8439 Specification

## Scenarios

### ChaCha20-Poly1305 RFC 8439 §2.4.2 stream ciphertext via AEAD wrapper

#### encrypt produces canonical §2.4.2 ciphertext bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined = chacha20_poly1305_encrypt(KEY_2_4_2, NONCE_2_4_2, PT_2_4_2, AAD_EMPTY)
val split = _split_ct_tag(combined)
expect(_bytes_eq(split.0, EXPECTED_CT_2_4_2)).to_equal(true)
```

</details>

#### output length is plaintext length + 16 (tag)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined = chacha20_poly1305_encrypt(KEY_2_4_2, NONCE_2_4_2, PT_2_4_2, AAD_EMPTY)
expect(combined.len()).to_equal(130u64)
```

</details>

### ChaCha20-Poly1305 RFC 8439 §2.8.2 canonical AEAD vector

#### encrypts plaintext to expected ciphertext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined = chacha20_poly1305_encrypt(KEY_2_8_2, NONCE_2_8_2, PT_2_8_2, AAD_2_8_2)
val split = _split_ct_tag(combined)
expect(_bytes_eq(split.0, EXPECTED_CT_2_8_2)).to_equal(true)
```

</details>

#### encrypts to expected Poly1305 tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Known-failing: impl tag diverges from canonical for 114-byte inputs.
# See doc/01_research/local/chacha_poly_tag_bug_2026-04-17.md
val combined = chacha20_poly1305_encrypt(KEY_2_8_2, NONCE_2_8_2, PT_2_8_2, AAD_2_8_2)
val split = _split_ct_tag(combined)
expect(_bytes_eq(split.1, EXPECTED_TAG_2_8_2)).to_equal(true)
```

</details>

#### decrypts canonical ciphertext+tag back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _decrypt_ok(KEY_2_8_2, NONCE_2_8_2, EXPECTED_CT_2_8_2, AAD_2_8_2, EXPECTED_TAG_2_8_2)
expect(_bytes_eq(pt, PT_2_8_2)).to_equal(true)
```

</details>

#### rejects a one-bit-flipped tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_tag = _corrupt(EXPECTED_TAG_2_8_2, 0u64)
expect(_decrypt_is_err(KEY_2_8_2, NONCE_2_8_2, EXPECTED_CT_2_8_2, AAD_2_8_2, bad_tag)).to_equal(true)
```

</details>

#### rejects corrupted AAD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_aad = _corrupt(AAD_2_8_2, 0u64)
expect(_decrypt_is_err(KEY_2_8_2, NONCE_2_8_2, EXPECTED_CT_2_8_2, bad_aad, EXPECTED_TAG_2_8_2)).to_equal(true)
```

</details>

#### rejects corrupted ciphertext

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_ct = _corrupt(EXPECTED_CT_2_8_2, 0u64)
expect(_decrypt_is_err(KEY_2_8_2, NONCE_2_8_2, bad_ct, AAD_2_8_2, EXPECTED_TAG_2_8_2)).to_equal(true)
```

</details>

### ChaCha20-Poly1305 RFC 8439 A.5 #5 (256-byte input, 4 ChaCha blocks)

#### output length is plaintext length + 16 (tag)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined = chacha20_poly1305_encrypt(KEY_A5_5, NONCE_A5_5, PT_A5_5, AAD_A5_5)
expect(combined.len()).to_equal(272u64)
```

</details>

#### roundtrip: decrypt recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined = chacha20_poly1305_encrypt(KEY_A5_5, NONCE_A5_5, PT_A5_5, AAD_A5_5)
val split = _split_ct_tag(combined)
val recovered = _decrypt_ok(KEY_A5_5, NONCE_A5_5, split.0, AAD_A5_5, split.1)
expect(_bytes_eq(recovered, PT_A5_5)).to_equal(true)
```

</details>

#### rejects a one-bit-flipped tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined = chacha20_poly1305_encrypt(KEY_A5_5, NONCE_A5_5, PT_A5_5, AAD_A5_5)
val split = _split_ct_tag(combined)
val bad_tag = _corrupt(split.1, 0u64)
expect(_decrypt_is_err(KEY_A5_5, NONCE_A5_5, split.0, AAD_A5_5, bad_tag)).to_equal(true)
```

</details>

#### rejects corrupted AAD

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined = chacha20_poly1305_encrypt(KEY_A5_5, NONCE_A5_5, PT_A5_5, AAD_A5_5)
val split = _split_ct_tag(combined)
val bad_aad = _corrupt(AAD_A5_5, 0u64)
expect(_decrypt_is_err(KEY_A5_5, NONCE_A5_5, split.0, bad_aad, split.1)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/chacha20_poly1305_rfc8439_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ChaCha20-Poly1305 RFC 8439 §2.4.2 stream ciphertext via AEAD wrapper
- ChaCha20-Poly1305 RFC 8439 §2.8.2 canonical AEAD vector
- ChaCha20-Poly1305 RFC 8439 A.5 #5 (256-byte input, 4 ChaCha blocks)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

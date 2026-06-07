# Aes Gcm Rfc Vectors Specification

> <details>

<!-- sdn-diagram:id=aes_gcm_rfc_vectors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes_gcm_rfc_vectors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes_gcm_rfc_vectors_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes_gcm_rfc_vectors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Gcm Rfc Vectors Specification

## Scenarios

### AES-256-GCM NIST CAVS gcmEncryptExtIV256 vectors

#### V1 encrypt: empty PT + empty AAD — tag matches NIST CAVS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val out = aes256_gcm_encrypt(_v1_key(), _v1_nonce(), empty, empty)
val ct = _split_ct(out, 0)
val tag = _split_tag(out, 0)
expect(ct.len()).to_equal(0)
expect(tag).to_equal(_v1_expected_tag())
```

</details>

#### V1 decrypt: correct tag succeeds with empty plaintext

1. AesGcmResult Ok
   - Expected: pt.len() equals `0`
2. AesGcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = aes256_gcm_decrypt(_v1_key(), _v1_nonce(), empty, empty, _v1_expected_tag())
match result:
    AesGcmResult.Ok(pt):
        expect(pt.len()).to_equal(0)
    AesGcmResult.Err(msg):
        fail("unexpected AES-GCM vector result branch")
```

</details>

#### V1 decrypt: corrupted tag is rejected

1. AesGcmResult Ok
2. fail
3. AesGcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_v1_expected_tag())
val result = aes256_gcm_decrypt(_v1_key(), _v1_nonce(), empty, empty, bad_tag)
match result:
    AesGcmResult.Ok(pt):
        fail("unexpected AES-GCM vector result branch")
    AesGcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### V2 encrypt: empty PT + 16-byte AAD — tag matches NIST CAVS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val out = aes256_gcm_encrypt(_v2_key(), _v2_nonce(), empty, _v2_aad())
val ct = _split_ct(out, 0)
val tag = _split_tag(out, 0)
expect(ct.len()).to_equal(0)
expect(tag).to_equal(_v2_expected_tag())
```

</details>

#### V2 decrypt: correct tag succeeds, wrong AAD is rejected

1. AesGcmResult Ok
   - Expected: pt.len() equals `0`
2. AesGcmResult Err
3. fail
4. AesGcmResult Ok
5. fail
6. AesGcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val ok = aes256_gcm_decrypt(_v2_key(), _v2_nonce(), empty, _v2_aad(), _v2_expected_tag())
match ok:
    AesGcmResult.Ok(pt):
        expect(pt.len()).to_equal(0)
    AesGcmResult.Err(msg):
        fail("unexpected AES-GCM vector result branch")
# wrong AAD must fail
val wrong_aad = _v1_nonce()  # reuse any 12-byte slice as wrong 12-byte AAD (length mismatch -> tag mismatch)
val bad = aes256_gcm_decrypt(_v2_key(), _v2_nonce(), empty, wrong_aad, _v2_expected_tag())
match bad:
    AesGcmResult.Ok(pt):
        fail("unexpected AES-GCM vector result branch")
    AesGcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### V3 encrypt: 16-byte PT, empty AAD — ciphertext and tag match NIST CAVS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val out = aes256_gcm_encrypt(_v3_key(), _v3_nonce(), _v3_plaintext(), empty)
val ct = _split_ct(out, 16)
val tag = _split_tag(out, 16)
expect(ct).to_equal(_v3_expected_ct())
expect(tag).to_equal(_v3_expected_tag())
```

</details>

#### V3 decrypt: correct tag returns original plaintext

1. AesGcmResult Ok
   - Expected: pt equals `_v3_plaintext()`
2. AesGcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = aes256_gcm_decrypt(_v3_key(), _v3_nonce(), _v3_expected_ct(), empty, _v3_expected_tag())
match result:
    AesGcmResult.Ok(pt):
        expect(pt).to_equal(_v3_plaintext())
    AesGcmResult.Err(msg):
        fail("unexpected AES-GCM vector result branch")
```

</details>

#### V3 decrypt: corrupted tag is rejected

1. AesGcmResult Ok
2. fail
3. AesGcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_v3_expected_tag())
val result = aes256_gcm_decrypt(_v3_key(), _v3_nonce(), _v3_expected_ct(), empty, bad_tag)
match result:
    AesGcmResult.Ok(pt):
        fail("unexpected AES-GCM vector result branch")
    AesGcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### V4 encrypt: 16-byte PT + 16-byte AAD — ciphertext and tag match NIST CAVS

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_gcm_encrypt(_v4_key(), _v4_nonce(), _v4_plaintext(), _v4_aad())
val ct = _split_ct(out, 16)
val tag = _split_tag(out, 16)
expect(ct).to_equal(_v4_expected_ct())
expect(tag).to_equal(_v4_expected_tag())
```

</details>

#### V4 decrypt: correct tag returns original plaintext

1. AesGcmResult Ok
   - Expected: pt equals `_v4_plaintext()`
2. AesGcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes256_gcm_decrypt(_v4_key(), _v4_nonce(), _v4_expected_ct(), _v4_aad(), _v4_expected_tag())
match result:
    AesGcmResult.Ok(pt):
        expect(pt).to_equal(_v4_plaintext())
    AesGcmResult.Err(msg):
        fail("unexpected AES-GCM vector result branch")
```

</details>

#### V4 decrypt: corrupted tag is rejected

1. AesGcmResult Ok
2. fail
3. AesGcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_tag = _corrupt_last_byte(_v4_expected_tag())
val result = aes256_gcm_decrypt(_v4_key(), _v4_nonce(), _v4_expected_ct(), _v4_aad(), bad_tag)
match result:
    AesGcmResult.Ok(pt):
        fail("unexpected AES-GCM vector result branch")
    AesGcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes_gcm_rfc_vectors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-256-GCM NIST CAVS gcmEncryptExtIV256 vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

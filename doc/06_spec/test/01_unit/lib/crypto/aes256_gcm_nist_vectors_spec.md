# Aes256 Gcm Nist Vectors Specification

> <details>

<!-- sdn-diagram:id=aes256_gcm_nist_vectors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes256_gcm_nist_vectors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes256_gcm_nist_vectors_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes256_gcm_nist_vectors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes256 Gcm Nist Vectors Specification

## Scenarios

### AES-256-GCM NIST SP 800-38D Appendix B vectors

#### TC13 encrypt: empty PT + empty AAD - tag matches NIST SP 800-38D B.13

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val out = aes256_gcm_encrypt(_tc13_key(), _tc13_nonce(), empty, empty)
val ct = _split_ct(out, 0)
val tag = _split_tag(out, 0)
expect(ct.len()).to_equal(0)
expect(tag).to_equal(_tc13_expected_tag())
```

</details>

#### TC13 decrypt: correct tag succeeds with empty plaintext

1. Aes256GcmResult Ok
   - Expected: data.len() equals `0`
2. Aes256GcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = aes256_gcm_decrypt(_tc13_key(), _tc13_nonce(), empty, empty, _tc13_expected_tag())
match result:
    Aes256GcmResult.Ok(data):
        expect(data.len()).to_equal(0)
    Aes256GcmResult.Err(msg):
        fail("unexpected AES-256-GCM vector result branch")
```

</details>

#### TC13 decrypt: corrupted tag is rejected

1. Aes256GcmResult Ok
2. fail
3. Aes256GcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc13_expected_tag())
val result = aes256_gcm_decrypt(_tc13_key(), _tc13_nonce(), empty, empty, bad_tag)
match result:
    Aes256GcmResult.Ok(data):
        fail("unexpected AES-256-GCM vector result branch")
    Aes256GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC14 encrypt: 16-byte zero PT, empty AAD - ciphertext and tag match NIST SP 800-38D B.14

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val out = aes256_gcm_encrypt(_tc14_key(), _tc14_nonce(), _tc14_plaintext(), empty)
val ct = _split_ct(out, 16)
val tag = _split_tag(out, 16)
expect(ct).to_equal(_tc14_expected_ct())
expect(tag).to_equal(_tc14_expected_tag())
```

</details>

#### TC14 decrypt: correct tag returns original plaintext

1. Aes256GcmResult Ok
   - Expected: data equals `_tc14_plaintext()`
2. Aes256GcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = aes256_gcm_decrypt(_tc14_key(), _tc14_nonce(), _tc14_expected_ct(), empty, _tc14_expected_tag())
match result:
    Aes256GcmResult.Ok(data):
        expect(data).to_equal(_tc14_plaintext())
    Aes256GcmResult.Err(msg):
        fail("unexpected AES-256-GCM vector result branch")
```

</details>

#### TC14 decrypt: corrupted tag is rejected

1. Aes256GcmResult Ok
2. fail
3. Aes256GcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc14_expected_tag())
val result = aes256_gcm_decrypt(_tc14_key(), _tc14_nonce(), _tc14_expected_ct(), empty, bad_tag)
match result:
    Aes256GcmResult.Ok(data):
        fail("unexpected AES-256-GCM vector result branch")
    Aes256GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC15 encrypt: 64-byte PT, empty AAD - ciphertext and tag match NIST SP 800-38D B.15

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val out = aes256_gcm_encrypt(_tc15_key(), _tc15_nonce(), _tc15_plaintext(), empty)
val ct = _split_ct(out, 64)
val tag = _split_tag(out, 64)
expect(ct).to_equal(_tc15_expected_ct())
expect(tag).to_equal(_tc15_expected_tag())
```

</details>

#### TC15 decrypt: correct tag returns original plaintext

1. Aes256GcmResult Ok
   - Expected: data equals `_tc15_plaintext()`
2. Aes256GcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = aes256_gcm_decrypt(_tc15_key(), _tc15_nonce(), _tc15_expected_ct(), empty, _tc15_expected_tag())
match result:
    Aes256GcmResult.Ok(data):
        expect(data).to_equal(_tc15_plaintext())
    Aes256GcmResult.Err(msg):
        fail("unexpected AES-256-GCM vector result branch")
```

</details>

#### TC15 decrypt: corrupted tag is rejected

1. Aes256GcmResult Ok
2. fail
3. Aes256GcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc15_expected_tag())
val result = aes256_gcm_decrypt(_tc15_key(), _tc15_nonce(), _tc15_expected_ct(), empty, bad_tag)
match result:
    Aes256GcmResult.Ok(data):
        fail("unexpected AES-256-GCM vector result branch")
    Aes256GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC16 encrypt: 60-byte PT, 20-byte AAD - ciphertext and tag match NIST SP 800-38D B.16

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_gcm_encrypt(_tc16_key(), _tc16_nonce(), _tc16_plaintext(), _tc16_aad())
val ct = _split_ct(out, 60)
val tag = _split_tag(out, 60)
expect(ct).to_equal(_tc16_expected_ct())
expect(tag).to_equal(_tc16_expected_tag())
```

</details>

#### TC16 decrypt: correct tag returns original plaintext

1. Aes256GcmResult Ok
   - Expected: data equals `_tc16_plaintext()`
2. Aes256GcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes256_gcm_decrypt(_tc16_key(), _tc16_nonce(), _tc16_expected_ct(), _tc16_aad(), _tc16_expected_tag())
match result:
    Aes256GcmResult.Ok(data):
        expect(data).to_equal(_tc16_plaintext())
    Aes256GcmResult.Err(msg):
        fail("unexpected AES-256-GCM vector result branch")
```

</details>

#### TC16 decrypt: corrupted tag is rejected

1. Aes256GcmResult Ok
2. fail
3. Aes256GcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_tag = _corrupt_last_byte(_tc16_expected_tag())
val result = aes256_gcm_decrypt(_tc16_key(), _tc16_nonce(), _tc16_expected_ct(), _tc16_aad(), bad_tag)
match result:
    Aes256GcmResult.Ok(data):
        fail("unexpected AES-256-GCM vector result branch")
    Aes256GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-256-GCM NIST SP 800-38D Appendix B vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

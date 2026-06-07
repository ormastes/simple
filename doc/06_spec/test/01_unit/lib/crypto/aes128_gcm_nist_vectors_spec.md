# Aes128 Gcm Nist Vectors Specification

> <details>

<!-- sdn-diagram:id=aes128_gcm_nist_vectors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes128_gcm_nist_vectors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes128_gcm_nist_vectors_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes128_gcm_nist_vectors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes128 Gcm Nist Vectors Specification

## Scenarios

### AES-128-GCM NIST SP 800-38D Appendix B vectors

#### TC1 encrypt: empty PT + empty AAD — tag matches NIST SP 800-38D B.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val out = aes128_gcm_encrypt(_tc1_key(), _tc1_nonce(), empty, empty)
val ct = _split_ct(out, 0)
val tag = _split_tag(out, 0)
expect(ct.len()).to_equal(0)
expect(tag).to_equal(_tc1_expected_tag())
```

</details>

#### TC1 decrypt: correct tag succeeds with empty plaintext

1. Aes128GcmResult Ok
   - Expected: data.len() equals `0`
2. Aes128GcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = aes128_gcm_decrypt(_tc1_key(), _tc1_nonce(), empty, empty, _tc1_expected_tag())
match result:
    Aes128GcmResult.Ok(data):
        expect(data.len()).to_equal(0)
    Aes128GcmResult.Err(msg):
        fail("unexpected AES-128-GCM vector result branch")
```

</details>

#### TC1 decrypt: corrupted tag is rejected

1. Aes128GcmResult Ok
2. fail
3. Aes128GcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc1_expected_tag())
val result = aes128_gcm_decrypt(_tc1_key(), _tc1_nonce(), empty, empty, bad_tag)
match result:
    Aes128GcmResult.Ok(data):
        fail("unexpected AES-128-GCM vector result branch")
    Aes128GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC2 encrypt: 16-byte zero PT, empty AAD — ciphertext and tag match NIST SP 800-38D B.2

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val out = aes128_gcm_encrypt(_tc2_key(), _tc2_nonce(), _tc2_plaintext(), empty)
val ct = _split_ct(out, 16)
val tag = _split_tag(out, 16)
expect(ct).to_equal(_tc2_expected_ct())
expect(tag).to_equal(_tc2_expected_tag())
```

</details>

#### TC2 decrypt: correct tag returns original plaintext

1. Aes128GcmResult Ok
   - Expected: data equals `_tc2_plaintext()`
2. Aes128GcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = aes128_gcm_decrypt(_tc2_key(), _tc2_nonce(), _tc2_expected_ct(), empty, _tc2_expected_tag())
match result:
    Aes128GcmResult.Ok(data):
        expect(data).to_equal(_tc2_plaintext())
    Aes128GcmResult.Err(msg):
        fail("unexpected AES-128-GCM vector result branch")
```

</details>

#### TC2 decrypt: corrupted tag is rejected

1. Aes128GcmResult Ok
2. fail
3. Aes128GcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc2_expected_tag())
val result = aes128_gcm_decrypt(_tc2_key(), _tc2_nonce(), _tc2_expected_ct(), empty, bad_tag)
match result:
    Aes128GcmResult.Ok(data):
        fail("unexpected AES-128-GCM vector result branch")
    Aes128GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC3 encrypt: 64-byte PT, empty AAD — ciphertext and tag match NIST SP 800-38D B.3

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val out = aes128_gcm_encrypt(_tc3_key(), _tc3_nonce(), _tc3_plaintext(), empty)
val ct = _split_ct(out, 64)
val tag = _split_tag(out, 64)
expect(ct).to_equal(_tc3_expected_ct())
expect(tag).to_equal(_tc3_expected_tag())
```

</details>

#### TC3 decrypt: correct tag returns original plaintext

1. Aes128GcmResult Ok
   - Expected: data equals `_tc3_plaintext()`
2. Aes128GcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = aes128_gcm_decrypt(_tc3_key(), _tc3_nonce(), _tc3_expected_ct(), empty, _tc3_expected_tag())
match result:
    Aes128GcmResult.Ok(data):
        expect(data).to_equal(_tc3_plaintext())
    Aes128GcmResult.Err(msg):
        fail("unexpected AES-128-GCM vector result branch")
```

</details>

#### TC3 decrypt: corrupted tag is rejected

1. Aes128GcmResult Ok
2. fail
3. Aes128GcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc3_expected_tag())
val result = aes128_gcm_decrypt(_tc3_key(), _tc3_nonce(), _tc3_expected_ct(), empty, bad_tag)
match result:
    Aes128GcmResult.Ok(data):
        fail("unexpected AES-128-GCM vector result branch")
    Aes128GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC4 encrypt: 60-byte PT, 20-byte AAD — ciphertext and tag match NIST SP 800-38D B.4

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes128_gcm_encrypt(_tc4_key(), _tc4_nonce(), _tc4_plaintext(), _tc4_aad())
val ct = _split_ct(out, 60)
val tag = _split_tag(out, 60)
expect(ct).to_equal(_tc4_expected_ct())
expect(tag).to_equal(_tc4_expected_tag())
```

</details>

#### TC4 decrypt: correct tag returns original plaintext

1. Aes128GcmResult Ok
   - Expected: data equals `_tc4_plaintext()`
2. Aes128GcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes128_gcm_decrypt(_tc4_key(), _tc4_nonce(), _tc4_expected_ct(), _tc4_aad(), _tc4_expected_tag())
match result:
    Aes128GcmResult.Ok(data):
        expect(data).to_equal(_tc4_plaintext())
    Aes128GcmResult.Err(msg):
        fail("unexpected AES-128-GCM vector result branch")
```

</details>

#### TC4 decrypt: corrupted tag is rejected

1. Aes128GcmResult Ok
2. fail
3. Aes128GcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_tag = _corrupt_last_byte(_tc4_expected_tag())
val result = aes128_gcm_decrypt(_tc4_key(), _tc4_nonce(), _tc4_expected_ct(), _tc4_aad(), bad_tag)
match result:
    Aes128GcmResult.Ok(data):
        fail("unexpected AES-128-GCM vector result branch")
    Aes128GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-128-GCM NIST SP 800-38D Appendix B vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

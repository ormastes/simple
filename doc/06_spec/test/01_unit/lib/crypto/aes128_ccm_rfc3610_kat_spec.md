# Aes128 Ccm Rfc3610 Kat Specification

> <details>

<!-- sdn-diagram:id=aes128_ccm_rfc3610_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes128_ccm_rfc3610_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes128_ccm_rfc3610_kat_spec -> std
aes128_ccm_rfc3610_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes128_ccm_rfc3610_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes128 Ccm Rfc3610 Kat Specification

## Scenarios

### AES-128-CCM RFC 3610 §8 reference vectors

#### Vector #1 encrypt: 8-byte AAD, 23-byte PT, M=8 — CT and tag match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes128_ccm_encrypt(_key_v1_4_7(), _v1_nonce(), _v1_aad(), _v1_plaintext(), 8)
val ct = _split_ct(out, _v1_plaintext().len())
val tag = _split_tag(out, _v1_plaintext().len())
expect(ct).to_equal(_v1_expected_ct())
expect(tag).to_equal(_v1_expected_tag())
```

</details>

#### Vector #1 decrypt: correct tag returns original plaintext

1.  v1 expected ct
2. Aes128CcmResult Ok
   - Expected: data equals `_v1_plaintext()`
3. Aes128CcmResult Err
   - Expected: msg equals `"")  # unreachable: encrypt must succeed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes128_ccm_decrypt(_key_v1_4_7(), _v1_nonce(), _v1_aad(),
                                 _v1_expected_ct(), _v1_expected_tag())
match result:
    Aes128CcmResult.Ok(data):
        expect(data).to_equal(_v1_plaintext())
    Aes128CcmResult.Err(msg):
        expect(msg).to_equal("")  # unreachable: encrypt must succeed
```

</details>

#### Vector #1 decrypt: corrupted ciphertext is rejected

1. bad ct,  v1 expected tag
2. Aes128CcmResult Ok
   - Expected: data.len() equals `99999)  # unreachable: must take Err branch`
3. Aes128CcmResult Err
   - Expected: msg contains `tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_ct = _corrupt_last_byte(_v1_expected_ct())
val result = aes128_ccm_decrypt(_key_v1_4_7(), _v1_nonce(), _v1_aad(),
                                 bad_ct, _v1_expected_tag())
match result:
    Aes128CcmResult.Ok(data):
        expect(data.len()).to_equal(99999)  # unreachable: must take Err branch
    Aes128CcmResult.Err(msg):
        expect(msg.contains("tag mismatch")).to_equal(true)
```

</details>

#### Vector #1 decrypt: modified AAD is rejected

1.  v1 expected ct
2. Aes128CcmResult Ok
   - Expected: data.len() equals `99999)  # unreachable: must take Err branch`
3. Aes128CcmResult Err
   - Expected: msg contains `tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_aad = _corrupt_last_byte(_v1_aad())
val result = aes128_ccm_decrypt(_key_v1_4_7(), _v1_nonce(), bad_aad,
                                 _v1_expected_ct(), _v1_expected_tag())
match result:
    Aes128CcmResult.Ok(data):
        expect(data.len()).to_equal(99999)  # unreachable: must take Err branch
    Aes128CcmResult.Err(msg):
        expect(msg.contains("tag mismatch")).to_equal(true)
```

</details>

#### Vector #4 encrypt: 12-byte AAD, 19-byte PT, M=8 — CT and tag match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes128_ccm_encrypt(_key_v1_4_7(), _v4_nonce(), _v4_aad(), _v4_plaintext(), 8)
val ct = _split_ct(out, _v4_plaintext().len())
val tag = _split_tag(out, _v4_plaintext().len())
expect(ct).to_equal(_v4_expected_ct())
expect(tag).to_equal(_v4_expected_tag())
```

</details>

#### Vector #4 decrypt: correct tag returns original plaintext

1.  v4 expected ct
2. Aes128CcmResult Ok
   - Expected: data equals `_v4_plaintext()`
3. Aes128CcmResult Err
   - Expected: msg equals `"")  # unreachable: encrypt must succeed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes128_ccm_decrypt(_key_v1_4_7(), _v4_nonce(), _v4_aad(),
                                 _v4_expected_ct(), _v4_expected_tag())
match result:
    Aes128CcmResult.Ok(data):
        expect(data).to_equal(_v4_plaintext())
    Aes128CcmResult.Err(msg):
        expect(msg).to_equal("")  # unreachable: encrypt must succeed
```

</details>

#### Vector #7 encrypt: M=10 (different tag length) — CT and tag match RFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes128_ccm_encrypt(_key_v1_4_7(), _v7_nonce(), _v7_aad(), _v7_plaintext(), 10)
val ct = _split_ct(out, _v7_plaintext().len())
val tag = _split_tag(out, _v7_plaintext().len())
expect(ct).to_equal(_v7_expected_ct())
expect(tag).to_equal(_v7_expected_tag())
```

</details>

#### Vector #7 decrypt: correct 10-byte tag returns original plaintext

1.  v7 expected ct
2. Aes128CcmResult Ok
   - Expected: data equals `_v7_plaintext()`
3. Aes128CcmResult Err
   - Expected: msg equals `"")  # unreachable: encrypt must succeed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes128_ccm_decrypt(_key_v1_4_7(), _v7_nonce(), _v7_aad(),
                                 _v7_expected_ct(), _v7_expected_tag())
match result:
    Aes128CcmResult.Ok(data):
        expect(data).to_equal(_v7_plaintext())
    Aes128CcmResult.Err(msg):
        expect(msg).to_equal("")  # unreachable: encrypt must succeed
```

</details>

#### Vector #7 decrypt: corrupted tag is rejected

1.  v7 expected ct
2. Aes128CcmResult Ok
   - Expected: data.len() equals `99999)  # unreachable: must take Err branch`
3. Aes128CcmResult Err
   - Expected: msg contains `tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_tag = _corrupt_last_byte(_v7_expected_tag())
val result = aes128_ccm_decrypt(_key_v1_4_7(), _v7_nonce(), _v7_aad(),
                                 _v7_expected_ct(), bad_tag)
match result:
    Aes128CcmResult.Ok(data):
        expect(data.len()).to_equal(99999)  # unreachable: must take Err branch
    Aes128CcmResult.Err(msg):
        expect(msg.contains("tag mismatch")).to_equal(true)
```

</details>

### AES-128-CCM edge cases
_Edge cases not covered by RFC 3610 §8: empty inputs and M=16 round-trip."_

#### empty plaintext + empty AAD round-trips at M=8

1. Aes128CcmResult Ok
   - Expected: data.len() equals `0`
2. Aes128CcmResult Err
   - Expected: msg equals `"")  # unreachable: encrypt must succeed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val nonce = _v1_nonce()
val key = _key_v1_4_7()
val out = aes128_ccm_encrypt(key, nonce, empty, empty, 8)
# output is just the 8-byte tag (no CT bytes)
expect(out.len()).to_equal(8)
val tag = _split_tag(out, 0)
val result = aes128_ccm_decrypt(key, nonce, empty, empty, tag)
match result:
    Aes128CcmResult.Ok(data):
        expect(data.len()).to_equal(0)
    Aes128CcmResult.Err(msg):
        expect(msg).to_equal("")  # unreachable: encrypt must succeed
```

</details>

#### empty AAD + non-empty PT round-trips at M=16

1. Aes128CcmResult Ok
   - Expected: data equals `pt`
2. Aes128CcmResult Err
   - Expected: msg equals `"")  # unreachable: encrypt must succeed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# M=16 has no RFC 3610 §8 KAT; round-trip-only.
val empty: [u8] = []
val nonce = _v1_nonce()
val key = _key_v1_4_7()
val pt = _v1_plaintext()
val out = aes128_ccm_encrypt(key, nonce, empty, pt, 16)
# output is 23 bytes CT + 16 bytes tag = 39 bytes total
expect(out.len()).to_equal(pt.len() + 16)
val ct = _split_ct(out, pt.len())
val tag = _split_tag(out, pt.len())
expect(tag.len()).to_equal(16)
val result = aes128_ccm_decrypt(key, nonce, empty, ct, tag)
match result:
    Aes128CcmResult.Ok(data):
        expect(data).to_equal(pt)
    Aes128CcmResult.Err(msg):
        expect(msg).to_equal("")  # unreachable: encrypt must succeed
```

</details>

#### M=16 detects single-bit ciphertext flip

1. Aes128CcmResult Ok
   - Expected: data.len() equals `99999)  # unreachable: must take Err branch`
2. Aes128CcmResult Err
   - Expected: msg contains `tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val nonce = _v1_nonce()
val key = _key_v1_4_7()
val pt = _v1_plaintext()
val out = aes128_ccm_encrypt(key, nonce, empty, pt, 16)
val ct = _split_ct(out, pt.len())
val tag = _split_tag(out, pt.len())
val bad_ct = _corrupt_last_byte(ct)
val result = aes128_ccm_decrypt(key, nonce, empty, bad_ct, tag)
match result:
    Aes128CcmResult.Ok(data):
        expect(data.len()).to_equal(99999)  # unreachable: must take Err branch
    Aes128CcmResult.Err(msg):
        expect(msg.contains("tag mismatch")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-128-CCM RFC 3610 §8 reference vectors
- AES-128-CCM edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

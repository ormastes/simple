# Aes Gcm Siv Rfc8452 Kat Specification

> 1.  tc1 key

<!-- sdn-diagram:id=aes_gcm_siv_rfc8452_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes_gcm_siv_rfc8452_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes_gcm_siv_rfc8452_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes_gcm_siv_rfc8452_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Gcm Siv Rfc8452 Kat Specification

## Scenarios

### AES-128-GCM-SIV RFC 8452 Appendix C.1

#### TC1: encrypt empty PT + empty AAD → 16-byte tag

1.  tc1 key
   - Expected: result.len() equals `16`
   - Expected: _equal_bytes(result, _tc1_expected()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes128_gcm_siv_encrypt(
    _tc1_key(), _tc1_nonce(), [], [])
expect(result.len()).to_equal(16)
expect(_equal_bytes(result, _tc1_expected())).to_equal(true)
```

</details>

#### TC1: decrypt round-trip

1. AesGcmSivResult Ok
   - Expected: data.len() equals `0`
2. AesGcmSivResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = aes128_gcm_siv_encrypt(_tc1_key(), _tc1_nonce(), [], [])
val dec = aes128_gcm_siv_decrypt(_tc1_key(), _tc1_nonce(), [], enc)
match dec:
    AesGcmSivResult.Ok(data):
        expect(data.len()).to_equal(0)
    AesGcmSivResult.Err(msg):
        fail("AES-128-GCM-SIV TC1 decrypt returned Err: {msg}")
```

</details>

#### TC2: encrypt 12-byte PT + empty AAD → 28 bytes

1.  tc2 key
   - Expected: result.len() equals `28`
   - Expected: _equal_bytes(result, _tc2_expected()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes128_gcm_siv_encrypt(
    _tc2_key(), _tc2_nonce(), [], _tc2_pt())
expect(result.len()).to_equal(28)
expect(_equal_bytes(result, _tc2_expected())).to_equal(true)
```

</details>

#### TC2: decrypt round-trip recovers plaintext

1. AesGcmSivResult Ok
   - Expected: _equal_bytes(data, _tc2_pt()) is true
2. AesGcmSivResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = aes128_gcm_siv_encrypt(_tc2_key(), _tc2_nonce(), [], _tc2_pt())
val dec = aes128_gcm_siv_decrypt(_tc2_key(), _tc2_nonce(), [], enc)
match dec:
    AesGcmSivResult.Ok(data):
        expect(_equal_bytes(data, _tc2_pt())).to_equal(true)
    AesGcmSivResult.Err(msg):
        fail("AES-128-GCM-SIV TC2 decrypt returned Err: {msg}")
```

</details>

#### TC2: decrypt with wrong key returns Err

1. AesGcmSivResult Ok
2. fail
3. AesGcmSivResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = aes128_gcm_siv_encrypt(_tc2_key(), _tc2_nonce(), [], _tc2_pt())
var bad_key: [u8] = [0x02u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
                      0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
val dec = aes128_gcm_siv_decrypt(bad_key, _tc2_nonce(), [], enc)
match dec:
    AesGcmSivResult.Ok(data):
        fail("AES-128-GCM-SIV TC2 decrypt accepted the wrong key")
    AesGcmSivResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

### AES-256-GCM-SIV RFC 8452 Appendix C.2

#### TC3: encrypt 12-byte PT + empty AAD → 28 bytes

1.  tc3 key
   - Expected: result.len() equals `28`
   - Expected: _equal_bytes(result, _tc3_expected()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes256_gcm_siv_encrypt(
    _tc3_key(), _tc3_nonce(), [], _tc3_pt())
expect(result.len()).to_equal(28)
expect(_equal_bytes(result, _tc3_expected())).to_equal(true)
```

</details>

#### TC3: decrypt round-trip recovers plaintext

1. AesGcmSivResult Ok
   - Expected: _equal_bytes(data, _tc3_pt()) is true
2. AesGcmSivResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = aes256_gcm_siv_encrypt(_tc3_key(), _tc3_nonce(), [], _tc3_pt())
val dec = aes256_gcm_siv_decrypt(_tc3_key(), _tc3_nonce(), [], enc)
match dec:
    AesGcmSivResult.Ok(data):
        expect(_equal_bytes(data, _tc3_pt())).to_equal(true)
    AesGcmSivResult.Err(msg):
        fail("AES-256-GCM-SIV TC3 decrypt returned Err: {msg}")
```

</details>

#### TC4: encrypt 16-byte PT + empty AAD → 32 bytes

1.  tc4 key
   - Expected: result.len() equals `32`
   - Expected: _equal_bytes(result, _tc4_expected()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes256_gcm_siv_encrypt(
    _tc4_key(), _tc4_nonce(), [], _tc4_pt())
expect(result.len()).to_equal(32)
expect(_equal_bytes(result, _tc4_expected())).to_equal(true)
```

</details>

#### TC4: decrypt round-trip recovers plaintext

1. AesGcmSivResult Ok
   - Expected: _equal_bytes(data, _tc4_pt()) is true
2. AesGcmSivResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = aes256_gcm_siv_encrypt(_tc4_key(), _tc4_nonce(), [], _tc4_pt())
val dec = aes256_gcm_siv_decrypt(_tc4_key(), _tc4_nonce(), [], enc)
match dec:
    AesGcmSivResult.Ok(data):
        expect(_equal_bytes(data, _tc4_pt())).to_equal(true)
    AesGcmSivResult.Err(msg):
        fail("AES-256-GCM-SIV TC4 decrypt returned Err: {msg}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes_gcm_siv_rfc8452_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-128-GCM-SIV RFC 8452 Appendix C.1
- AES-256-GCM-SIV RFC 8452 Appendix C.2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

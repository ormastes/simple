# Chacha20 Poly1305 Cipher Suite Specification

> <details>

<!-- sdn-diagram:id=chacha20_poly1305_cipher_suite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chacha20_poly1305_cipher_suite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chacha20_poly1305_cipher_suite_spec -> std
chacha20_poly1305_cipher_suite_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chacha20_poly1305_cipher_suite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Poly1305 Cipher Suite Specification

## Scenarios

### TLS_CHACHA20_POLY1305_SHA256 (0x1303) cipher suite landing

#### CIPHER_CHACHA20_POLY1305_SHA256 constant has IANA value 0x1303

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CIPHER_CHACHA20_POLY1305_SHA256).to_equal(0x1303u16)
```

</details>

#### CIPHER_AES_128_GCM_SHA256 constant remains at IANA value 0x1301

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Sanity check — the existing suite must not have shifted.
expect(CIPHER_AES_128_GCM_SHA256).to_equal(0x1301u16)
```

</details>

#### CIPHER_AES_256_GCM_SHA384 constant remains at IANA value 0x1302

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Sanity check — the existing T21 suite must not have shifted.
expect(CIPHER_AES_256_GCM_SHA384).to_equal(0x1302u16)
```

</details>

#### ClientHello cipher_suites bytes advertise 0x1301, 0x1302 and 0x1303

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The on-the-wire byte sequence for the cipher_suites list should
# contain {0x13,0x01,0x13,0x02,0x13,0x03} for the 3 TLS 1.3 suites
# per RFC 8446 §9.1.
val ch = _ch_bytes()
expect(_has_two_byte_subseq(ch, 0x13u8, 0x01u8)).to_equal(true)
expect(_has_two_byte_subseq(ch, 0x13u8, 0x02u8)).to_equal(true)
expect(_has_two_byte_subseq(ch, 0x13u8, 0x03u8)).to_equal(true)
```

</details>

#### ChaCha20-Poly1305 encrypt produces ciphertext || 16-byte tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _chacha_key()
val out = chacha20_poly1305_encrypt(key, _zero_nonce(), _plaintext_demo(), _aad_demo())
# 32-byte plaintext + 16-byte tag = 48 bytes
expect(out.len()).to_equal(48)
```

</details>

#### ChaCha20-Poly1305 round-trip recovers plaintext

1. Chacha20Poly1305Result Ok
   - Expected: _bytes_equal(data, pt) is true
2. Chacha20Poly1305Result Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _chacha_key()
val nonce = _zero_nonce()
val pt = _plaintext_demo()
val aad = _aad_demo()

val packed = chacha20_poly1305_encrypt(key, nonce, pt, aad)
val ct = _split_ct(packed, pt.len().to_i64())
val tag = _split_tag(packed, pt.len().to_i64())

val result = chacha20_poly1305_decrypt(key, nonce, ct, aad, tag)
match result:
    Chacha20Poly1305Result.Ok(data):
        expect(_bytes_equal(data, pt)).to_equal(true)
    Chacha20Poly1305Result.Err(msg):
        fail("ChaCha20-Poly1305 round-trip returned Err: {msg}")
```

</details>

#### ChaCha20-Poly1305 tag-corruption is rejected

1. bad tag push
2. bad tag push
3. Chacha20Poly1305Result Ok
4. fail
5. Chacha20Poly1305Result Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _chacha_key()
val nonce = _zero_nonce()
val pt = _plaintext_demo()
val aad = _aad_demo()

val packed = chacha20_poly1305_encrypt(key, nonce, pt, aad)
val ct = _split_ct(packed, pt.len().to_i64())
val tag = _split_tag(packed, pt.len().to_i64())
var bad_tag: [u8] = []
var i: i64 = 0
while i < tag.len():
    if i == tag.len() - 1:
        bad_tag.push(tag[i] ^ 0xFFu8)
    else:
        bad_tag.push(tag[i])
    i = i + 1

val result = chacha20_poly1305_decrypt(key, nonce, ct, bad_tag, bad_tag)
match result:
    Chacha20Poly1305Result.Ok(data):
        fail("ChaCha20-Poly1305 accepted a corrupted tag")
    Chacha20Poly1305Result.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### record13_make_nonce: seq_num=0 yields the IV unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iv = _record_iv()
val nonce = record13_make_nonce(iv, 0u64)
expect(nonce.len()).to_equal(12)
# XOR with zero counter is identity.
expect(_bytes_equal(nonce, iv)).to_equal(true)
```

</details>

#### record13_make_nonce: seq_num=1 differs from seq_num=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iv = _record_iv()
val n0 = record13_make_nonce(iv, 0u64)
val n1 = record13_make_nonce(iv, 1u64)
expect(n1.len()).to_equal(12)
# Different sequence numbers MUST produce different per-record nonces.
expect(_bytes_equal(n0, n1)).to_equal(false)
```

</details>

#### record13_encrypt_chacha20_poly1305 wraps the AEAD output in a TLS 1.3 record

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rk = RecordKey(key: _chacha_key(), iv: _record_iv())
val pt = _plaintext_demo()
val record = record13_encrypt_chacha20_poly1305(rk, 0u64, 0x17u8, pt)
# 5-byte header + (33-byte inner = 32 pt + 1 ct byte) + 16-byte tag = 54 bytes
expect(record.len()).to_equal(54)
# TLS record header bytes
expect(record[0]).to_equal(0x17u8)
expect(record[1]).to_equal(0x03u8)
expect(record[2]).to_equal(0x03u8)
```

</details>

#### record13 ChaCha20-Poly1305 round-trip recovers content_type + data with seq_num=0

1. RecordResult Ok
   - Expected: content_type.to_u64() equals `0x17u64`
   - Expected: _bytes_equal(data, pt) is true
2. RecordResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rk = RecordKey(key: _chacha_key(), iv: _record_iv())
val pt = _plaintext_demo()
val record = record13_encrypt_chacha20_poly1305(rk, 0u64, 0x17u8, pt)
val result = record13_decrypt_chacha20_poly1305(rk, 0u64, record)
match result:
    RecordResult.Ok(content_type, data):
        expect(content_type.to_u64()).to_equal(0x17u64)
        expect(_bytes_equal(data, pt)).to_equal(true)
    RecordResult.Err(msg):
        fail("record13 ChaCha20-Poly1305 seq_num=0 round-trip returned Err: {msg}")
```

</details>

#### record13 ChaCha20-Poly1305 round-trip with seq_num=1 (per-record nonce derivation)

1. RecordResult Ok
   - Expected: content_type.to_u64() equals `0x17u64`
   - Expected: _bytes_equal(data, pt) is true
2. RecordResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rk = RecordKey(key: _chacha_key(), iv: _record_iv())
val pt = _plaintext_demo()
val record = record13_encrypt_chacha20_poly1305(rk, 1u64, 0x17u8, pt)
val result = record13_decrypt_chacha20_poly1305(rk, 1u64, record)
match result:
    RecordResult.Ok(content_type, data):
        expect(content_type.to_u64()).to_equal(0x17u64)
        expect(_bytes_equal(data, pt)).to_equal(true)
    RecordResult.Err(msg):
        fail("record13 ChaCha20-Poly1305 seq_num=1 round-trip returned Err: {msg}")
```

</details>

#### record13 ChaCha20-Poly1305 mismatched seq_num is rejected (auth tag)

1. RecordResult Ok
2. fail
3. RecordResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rk = RecordKey(key: _chacha_key(), iv: _record_iv())
val pt = _plaintext_demo()
val record = record13_encrypt_chacha20_poly1305(rk, 0u64, 0x17u8, pt)
# Decrypt with the wrong sequence number — nonce is XOR'd with seq_num,
# so the AEAD tag MUST fail to authenticate.
val result = record13_decrypt_chacha20_poly1305(rk, 1u64, record)
match result:
    RecordResult.Ok(content_type, data):
        fail("record13 ChaCha20-Poly1305 accepted a mismatched sequence number")
    RecordResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### record13_encrypt_for_suite dispatches 0x1303 to ChaCha20-Poly1305

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rk = RecordKey(key: _chacha_key(), iv: _record_iv())
val pt = _plaintext_demo()
val via_dispatch = record13_encrypt_for_suite(
    CIPHER_CHACHA20_POLY1305_SHA256, rk, 0u64, 0x17u8, pt
)
val direct = record13_encrypt_chacha20_poly1305(rk, 0u64, 0x17u8, pt)
expect(_bytes_equal(via_dispatch, direct)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/chacha20_poly1305_cipher_suite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TLS_CHACHA20_POLY1305_SHA256 (0x1303) cipher suite landing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

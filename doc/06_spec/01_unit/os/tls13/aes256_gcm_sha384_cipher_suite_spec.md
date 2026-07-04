# Aes256 Gcm Sha384 Cipher Suite Specification

> <details>

<!-- sdn-diagram:id=aes256_gcm_sha384_cipher_suite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes256_gcm_sha384_cipher_suite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes256_gcm_sha384_cipher_suite_spec -> std
aes256_gcm_sha384_cipher_suite_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes256_gcm_sha384_cipher_suite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes256 Gcm Sha384 Cipher Suite Specification

## Scenarios

### TLS_AES_256_GCM_SHA384 (0x1302) cipher suite landing

#### CIPHER_AES_256_GCM_SHA384 constant has IANA value 0x1302

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CIPHER_AES_256_GCM_SHA384).to_equal(0x1302u16)
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

#### ClientHello cipher_suites bytes advertise 0x1301 then 0x1302

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The on-the-wire byte sequence for the cipher_suites list should
# contain {0x13,0x01,0x13,0x02} consecutively for the 2 mandatory
# TLS 1.3 suites per RFC 8446 §9.1.
val ch = _ch_bytes()
# 0x13 0x01 (TLS_AES_128_GCM_SHA256) appears
expect(_has_two_byte_subseq(ch, 0x13u8, 0x01u8)).to_equal(true)
# 0x13 0x02 (TLS_AES_256_GCM_SHA384) appears
expect(_has_two_byte_subseq(ch, 0x13u8, 0x02u8)).to_equal(true)
```

</details>

#### AES-256-GCM encrypt produces ciphertext || 16-byte tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _zeros_n(32)
val out = aes256_gcm_encrypt(key, _zero_nonce(), _plaintext_demo(), _aad_demo())
# 32-byte plaintext + 16-byte tag = 48 bytes
expect(out.len()).to_equal(48)
```

</details>

#### AES-256-GCM round-trip recovers plaintext for synthetic record

1. Aes256GcmResult Ok
   - Expected: data equals `pt`
2. Aes256GcmResult Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _zeros_n(32)
val nonce = _zero_nonce()
val pt = _plaintext_demo()
val aad = _aad_demo()

val packed = aes256_gcm_encrypt(key, nonce, pt, aad)
val ct = _split_ct(packed, pt.len().to_i64())
val tag = _split_tag(packed, pt.len().to_i64())

val result = aes256_gcm_decrypt(key, nonce, ct, aad, tag)
match result:
    Aes256GcmResult.Ok(data):
        expect(data).to_equal(pt)
    Aes256GcmResult.Err(msg):
        fail("AES-256-GCM round-trip returned Err: {msg}")
```

</details>

#### AES-256-GCM tag-corruption is rejected

1. bad tag push
2. bad tag push
3. Aes256GcmResult Ok
4. fail
5. Aes256GcmResult Err
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _zeros_n(32)
val nonce = _zero_nonce()
val pt = _plaintext_demo()
val aad = _aad_demo()

val packed = aes256_gcm_encrypt(key, nonce, pt, aad)
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

val result = aes256_gcm_decrypt(key, nonce, ct, aad, bad_tag)
match result:
    Aes256GcmResult.Ok(data):
        fail("AES-256-GCM accepted a corrupted authentication tag")
    Aes256GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### SHA-384 early_secret has 48-byte length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val es = tls13_early_secret_sha384()
expect(es.len()).to_equal(48)
```

</details>

#### SHA-384 handshake_secret has 48-byte length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val es = tls13_early_secret_sha384()
val hs = tls13_handshake_secret_sha384(es, _dhe_shared())
expect(hs.len()).to_equal(48)
```

</details>

#### SHA-384 handshake_secret is deterministic for fixed inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val es = tls13_early_secret_sha384()
val hs1 = tls13_handshake_secret_sha384(es, _dhe_shared())
val hs2 = tls13_handshake_secret_sha384(es, _dhe_shared())
expect(hs1).to_equal(hs2)
```

</details>

#### SHA-384 traffic keys produce 32-byte AES-256 key + 12-byte IV

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val traffic_secret = _zeros_n(48)
val tk = tls13_traffic_keys_sha384(traffic_secret)
expect(tk.key.len()).to_equal(32)
expect(tk.iv.len()).to_equal(12)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/aes256_gcm_sha384_cipher_suite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TLS_AES_256_GCM_SHA384 (0x1302) cipher suite landing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

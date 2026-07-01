# OS Crypto Reference Signature Specification

> Cross-check every FFI-backed signature primitive against `/usr/bin/openssl`. RSA signing is deterministic, but OpenSSL signature readback currently hits the runtime byte-array Option marshalling path, so the regression check uses OpenSSL verification of Simple-produced signatures across representative messages instead of reading OpenSSL-produced signature bytes back into Simple.

<!-- sdn-diagram:id=os_crypto_ref_signature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_crypto_ref_signature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_crypto_ref_signature_spec -> std
os_crypto_ref_signature_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_crypto_ref_signature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# OS Crypto Reference Signature Specification

Cross-check every FFI-backed signature primitive against `/usr/bin/openssl`. RSA signing is deterministic, but OpenSSL signature readback currently hits the runtime byte-array Option marshalling path, so the regression check uses OpenSSL verification of Simple-produced signatures across representative messages instead of reading OpenSSL-produced signature bytes back into Simple.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/03_system/os/os_crypto_ref_signature_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Cross-check every FFI-backed signature primitive against `/usr/bin/openssl`.
RSA signing is deterministic, but OpenSSL signature readback currently hits
the runtime byte-array Option marshalling path, so the regression check uses
OpenSSL verification of Simple-produced signatures across representative
messages instead of reading OpenSSL-produced signature bytes back into Simple.

OpenSSL-backed checks are gated on `_openssl_signature_present()`.  If usable
OpenSSL 3+ is absent the affected tests pass vacuously.

tag: slow, system, crypto

## Scenarios

### os_crypto_ref_signature: RSA-SHA2-256 OpenSSL cross-check

#### skips entire suite when openssl is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
```

</details>

#### sign Hello World: Simple signature verifies with openssl

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_hello()
    val simple_sig = _sign_rsa256(pkcs8, msg)
    expect(simple_sig.len() > 0)
    expect(_openssl_rsa_verify_sha256(spki, msg, simple_sig))
```

</details>

#### sign empty message: Simple signature verifies with openssl

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_empty()
    val simple_sig = _sign_rsa256(pkcs8, msg)
    expect(simple_sig.len() > 0)
    expect(_openssl_rsa_verify_sha256(spki, msg, simple_sig))
```

</details>

#### sign 1 KB: Simple signature verifies with openssl

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _make_1kb()
    val simple_sig = _sign_rsa256(pkcs8, msg)
    expect(simple_sig.len() > 0)
    expect(_openssl_rsa_verify_sha256(spki, msg, simple_sig))
```

</details>

#### round-trip: Simple sign -> Simple verify -> true

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_hello()
    val sig = _sign_rsa256(pkcs8, msg)
    expect(sig.len() > 0)
    val ok = rsa_sha256_verify(spki, msg, sig)
    expect(ok)
```

</details>

#### cross-verify: Simple sign -> openssl verify -> success

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_hello()
    val sig = _sign_rsa256(pkcs8, msg)
    expect(sig.len() > 0)
    val ok = _openssl_rsa_verify_sha256(spki, msg, sig)
    expect(ok)
```

</details>

#### negative: tampered signature -> Simple verify = false

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_hello()
    val sig = _sign_rsa256(pkcs8, msg)
    if sig.len() == 0:
        expect(false)
    else:
        val bad_sig = _flip_first_byte(sig, 0xFF)
        val ok = rsa_sha256_verify(spki, msg, bad_sig)
        expect(not (ok))
```

</details>

#### large (4 KiB) message: sign + verify succeed

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _make_64kb()
    val sig = _sign_rsa256(pkcs8, msg)
    expect(sig.len() > 0)
    val ok = rsa_sha256_verify(spki, msg, sig)
    expect(ok)
```

</details>

### os_crypto_ref_signature: RSA-SHA2-512 OpenSSL cross-check

#### sign Hello World: Simple signature verifies with openssl

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_hello()
    val simple_sig = _sign_rsa512(pkcs8, msg)
    expect(simple_sig.len() > 0)
    expect(_openssl_rsa_verify_sha512(spki, msg, simple_sig))
```

</details>

#### sign empty message: Simple signature verifies with openssl

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_empty()
    val simple_sig = _sign_rsa512(pkcs8, msg)
    expect(simple_sig.len() > 0)
    expect(_openssl_rsa_verify_sha512(spki, msg, simple_sig))
```

</details>

#### sign 1 KB: Simple signature verifies with openssl

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _make_1kb()
    val simple_sig = _sign_rsa512(pkcs8, msg)
    expect(simple_sig.len() > 0)
    expect(_openssl_rsa_verify_sha512(spki, msg, simple_sig))
```

</details>

#### round-trip: Simple sign -> Simple verify -> true

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_hello()
    val sig = _sign_rsa512(pkcs8, msg)
    expect(sig.len() > 0)
    val ok = rsa_sha512_verify(spki, msg, sig)
    expect(ok)
```

</details>

#### cross-verify: Simple sign -> openssl verify -> success

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_hello()
    val sig = _sign_rsa512(pkcs8, msg)
    expect(sig.len() > 0)
    val ok = _openssl_rsa_verify_sha512(spki, msg, sig)
    expect(ok)
```

</details>

#### negative: tampered signature -> Simple verify = false

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _msg_hello()
    val sig = _sign_rsa512(pkcs8, msg)
    if sig.len() == 0:
        expect(false)
    else:
        val bad_sig = _flip_first_byte(sig, 0xFF)
        val ok = rsa_sha512_verify(spki, msg, bad_sig)
        expect(not (ok))
```

</details>

#### large (4 KiB) message: sign + verify succeed

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
    val spki = hex_to_bytes(RSA_SPKI_HEX)
    val msg = _make_64kb()
    val sig = _sign_rsa512(pkcs8, msg)
    expect(sig.len() > 0)
    val ok = rsa_sha512_verify(spki, msg, sig)
    expect(ok)
```

</details>

### os_crypto_ref_signature: ECDSA-SHA2-NISTP256 cross-check

#### same (key, msg) signed twice produces different signatures

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(EC_PKCS8_HEX)
    val msg = _msg_hello()
    val sig1 = _sign_ecdsa_p256(pkcs8, msg)
    val sig2 = _sign_ecdsa_p256(pkcs8, msg)
    expect(sig1.len()).to_equal(64)
    expect(sig2.len()).to_equal(64)
    # Non-deterministic: sigs should differ (astronomically unlikely to collide)
    expect(not (_bytes_eq(sig1, sig2)))
```

</details>

#### sign then Simple verify -> true (sig1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(EC_PKCS8_HEX)
    val spki = hex_to_bytes(EC_RAW_POINT_HEX)
    val msg = _msg_hello()
    val sig = _sign_ecdsa_p256(pkcs8, msg)
    expect(sig.len()).to_equal(64)
    val ok = ecdsa_p256_verify(spki, msg, sig)
    expect(ok)
```

</details>

#### second independent signature also verifies via Simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(EC_PKCS8_HEX)
    val spki = hex_to_bytes(EC_RAW_POINT_HEX)
    val msg = _msg_hello()
    val sig = _sign_ecdsa_p256(pkcs8, msg)
    val sig2 = _sign_ecdsa_p256(pkcs8, msg)
    val ok1 = ecdsa_p256_verify(spki, msg, sig)
    val ok2 = ecdsa_p256_verify(spki, msg, sig2)
    expect(ok1)
    expect(ok2)
```

</details>

#### Simple sign (fixed64) -> DER -> openssl verify -> success

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(EC_PKCS8_HEX)
    val spki = hex_to_bytes(EC_SPKI_HEX)
    val msg = _msg_hello()
    val sig_fixed = _sign_ecdsa_p256(pkcs8, msg)
    expect(sig_fixed.len()).to_equal(64)
    val sig_der = _fixed64_to_der(sig_fixed)
    expect(sig_der.len() > 8)
    val ok = openssl_ecdsa_p256_verify_der(spki, msg, sig_der)
    expect(ok)
```

</details>

#### DER-converted signature from 1 KB message verifies via openssl

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(EC_PKCS8_HEX)
    val spki = hex_to_bytes(EC_SPKI_HEX)
    val msg = _make_1kb()
    val sig_fixed = _sign_ecdsa_p256(pkcs8, msg)
    val sig_der = _fixed64_to_der(sig_fixed)
    val ok = openssl_ecdsa_p256_verify_der(spki, msg, sig_der)
    expect(ok)
```

</details>

#### negative: flip bit in message -> Simple verify = false

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(EC_PKCS8_HEX)
    val spki = hex_to_bytes(EC_RAW_POINT_HEX)
    val msg = _msg_hello()
    val sig = _sign_ecdsa_p256(pkcs8, msg)
    # Corrupt first byte of message
    val bad_msg = _flip_first_byte(msg, 0x01)
    val ok = ecdsa_p256_verify(spki, bad_msg, sig)
    expect(not (ok))
```

</details>

#### empty message: ECDSA sign + Simple verify succeed

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(EC_PKCS8_HEX)
    val spki = hex_to_bytes(EC_RAW_POINT_HEX)
    val msg = _msg_empty()
    val sig = _sign_ecdsa_p256(pkcs8, msg)
    expect(sig.len()).to_equal(64)
    val ok = ecdsa_p256_verify(spki, msg, sig)
    expect(ok)
```

</details>

#### large (4 KiB) message: ECDSA sign + Simple verify succeed

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pkcs8 = hex_to_bytes(EC_PKCS8_HEX)
    val spki = hex_to_bytes(EC_RAW_POINT_HEX)
    val msg = _make_64kb()
    val sig = _sign_ecdsa_p256(pkcs8, msg)
    expect(sig.len()).to_equal(64)
    val ok = ecdsa_p256_verify(spki, msg, sig)
    expect(ok)
```

</details>

### os_crypto_ref_signature: Ed25519 verify cross-check

#### RFC 8032 TEST 2: rt_ed25519_verify returns 1 for known-good vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = hex_to_bytes(ED25519_PK_HEX)
val msg = hex_to_bytes(ED25519_MSG_HEX)
val sig = hex_to_bytes(ED25519_SIG_HEX)
val result = rt_ed25519_verify(msg, pk, sig)
expect(result).to_equal(1)
```

</details>

#### RFC 8032 TEST 2: ed25519_verify wrapper returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = hex_to_bytes(ED25519_PK_HEX)
val msg = hex_to_bytes(ED25519_MSG_HEX)
val sig = hex_to_bytes(ED25519_SIG_HEX)
val ok = ed25519_verify(pk, msg, sig)
expect(ok)
```

</details>

#### RFC 8032 TEST 2: openssl pkeyutl -verify returns success

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _openssl_signature_present():
    expect(not (_openssl_signature_present()))
else:
    val pk = hex_to_bytes(ED25519_PK_HEX)
    val msg = hex_to_bytes(ED25519_MSG_HEX)
    val sig = hex_to_bytes(ED25519_SIG_HEX)
    val spki = hex_to_bytes(ED25519_SPKI_HEX)
    val ok = _openssl_ed25519_verify(spki, msg, sig)
    expect(ok)
```

</details>

#### negative: wrong public key -> ed25519_verify = false

1. bad pk push


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = hex_to_bytes(ED25519_PK_HEX)
val msg = hex_to_bytes(ED25519_MSG_HEX)
val sig = hex_to_bytes(ED25519_SIG_HEX)
# Use EC pubkey bytes (wrong type/length) as wrong pubkey
var bad_pk: [u8] = []
var i: u64 = 0
while i < 32:
    bad_pk.push((pk[i].to_i64() xor 0xFF).to_u8())
    i = i + 1
val ok = ed25519_verify(bad_pk, msg, sig)
expect(not (ok))
```

</details>

#### negative: corrupted signature -> ed25519_verify = false

1. bad sig push
2. bad sig push


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = hex_to_bytes(ED25519_PK_HEX)
val msg = hex_to_bytes(ED25519_MSG_HEX)
val sig = hex_to_bytes(ED25519_SIG_HEX)
var bad_sig: [u8] = []
bad_sig.push((sig[0].to_i64() xor 0x01).to_u8())
var i: u64 = 1
while i < sig.len():
    bad_sig.push(sig[i])
    i = i + 1
val ok = ed25519_verify(pk, msg, bad_sig)
expect(not (ok))
```

</details>

#### negative: modified message -> ed25519_verify = false

1. bad msg push


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = hex_to_bytes(ED25519_PK_HEX)
val msg = hex_to_bytes(ED25519_MSG_HEX)
val sig = hex_to_bytes(ED25519_SIG_HEX)
var bad_msg: [u8] = []
bad_msg.push((msg[0].to_i64() xor 0x01).to_u8())
val ok = ed25519_verify(pk, bad_msg, sig)
expect(not (ok))
```

</details>

### os_crypto_ref_signature: edge cases and negative coverage

#### malformed PKCS#8 -> rsa_sha256_sign returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = hex_to_bytes(BAD_PKCS8_HEX)
val msg = _msg_hello()
val sig = _sign_rsa256(bad, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### malformed PKCS#8 -> rsa_sha512_sign returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = hex_to_bytes(BAD_PKCS8_HEX)
val msg = _msg_hello()
val sig = _sign_rsa512(bad, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### malformed PKCS#8 -> ecdsa_p256_sign returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = hex_to_bytes(BAD_PKCS8_HEX)
val msg = _msg_hello()
val sig = _sign_ecdsa_p256(bad, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### wrong-type PKCS#8 (ECDSA key) -> rsa_sha256_sign returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ec_pkcs8 = hex_to_bytes(WRONG_TYPE_PKCS8_HEX)
val msg = _msg_hello()
val sig = _sign_rsa256(ec_pkcs8, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### wrong-type PKCS#8 (ECDSA key) -> rsa_sha512_sign returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ec_pkcs8 = hex_to_bytes(WRONG_TYPE_PKCS8_HEX)
val msg = _msg_hello()
val sig = _sign_rsa512(ec_pkcs8, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### wrong-type PKCS#8 (RSA key) -> ecdsa_p256_sign returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rsa_pkcs8 = hex_to_bytes(RSA_PKCS8_HEX)
val msg = _msg_hello()
val sig = _sign_ecdsa_p256(rsa_pkcs8, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### RSA 1024-bit key -> rsa_sha256_sign returns empty (ring min-size check)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val small_pkcs8 = hex_to_bytes(RSA_1024_PKCS8_HEX)
val msg = _msg_hello()
val sig = _sign_rsa256(small_pkcs8, msg)
expect(sig.len()).to_equal(0)
```

</details>

#### RSA verify with empty signature -> false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki = hex_to_bytes(RSA_SPKI_HEX)
val msg = _msg_hello()
var empty_sig: [u8] = []
val ok = rsa_sha256_verify(spki, msg, empty_sig)
expect(not (ok))
```

</details>

#### ECDSA verify with truncated 63-byte signature -> false

1. bad sig push


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki = hex_to_bytes(EC_SPKI_HEX)
val msg = _msg_hello()
var bad_sig: [u8] = []
var i: u64 = 0
while i < 63:
    bad_sig.push(0xAA)
    i = i + 1
val ok = ecdsa_p256_verify(spki, msg, bad_sig)
expect(not (ok))
```

</details>

#### ed25519 verify with empty signature -> false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = hex_to_bytes(ED25519_PK_HEX)
val msg = hex_to_bytes(ED25519_MSG_HEX)
var empty_sig: [u8] = []
val ok = ed25519_verify(pk, msg, empty_sig)
expect(not (ok))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# OS Crypto Reference Primitives Specification

> Byte-exact cross-check of the pure-Simple cryptographic primitives (those with no OS-level runtime FFI) against RFC known-answer test vectors, and where possible against `/usr/bin/openssl`.

<!-- sdn-diagram:id=os_crypto_ref_primitives_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_crypto_ref_primitives_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_crypto_ref_primitives_spec -> std
os_crypto_ref_primitives_spec -> os
os_crypto_ref_primitives_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_crypto_ref_primitives_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# OS Crypto Reference Primitives Specification

Byte-exact cross-check of the pure-Simple cryptographic primitives (those with no OS-level runtime FFI) against RFC known-answer test vectors, and where possible against `/usr/bin/openssl`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Complete |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/os/os_crypto_ref_primitives_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Byte-exact cross-check of the pure-Simple cryptographic primitives (those with
no OS-level runtime FFI) against RFC known-answer test vectors, and where
possible against `/usr/bin/openssl`.

**Module coverage:**
- ChaCha20 stream cipher (RFC 7539 §2.4.2) — pure Simple, fully testable
- Poly1305 MAC (RFC 7539 §2.5.2) — pure Simple, fully testable
- ChaCha20-Poly1305 AEAD (RFC 7539 §2.8.2) — pure Simple, fully testable
- X25519 scalar multiplication (RFC 7748) — pure Simple, interpreter-safe

**Excluded from this file** (all wrap OS-level rt_* externs, not pure Simple;
tested in other suites that run under native compile or baremetal):
- SHA-256, SHA-512, HMAC-SHA-256 (use rt_sha256_H / rt_sha512_H)
- AES-256-GCM, AES-128-GCM (use rt_aes*)
- Ed25519 (uses rt_ed25519_keypair / rt_ed25519_sign)

## Scenarios

### OS Crypto Ref: ChaCha20 stream cipher

#### ChaCha20 RFC 7539: output length equals plaintext length

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct = chacha20_encrypt(key, 1, nonce, pt)
expect(ct.len()).to_equal(114)
```

</details>

#### ChaCha20 RFC 7539: ciphertext byte[0] == 0x6e

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct = chacha20_encrypt(key, 1, nonce, pt)
expect(ct[0]).to_equal(0x6e)
```

</details>

#### ChaCha20 RFC 7539: ciphertext byte[1] == 0x2e

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct = chacha20_encrypt(key, 1, nonce, pt)
expect(ct[1]).to_equal(0x2e)
```

</details>

#### ChaCha20 RFC 7539: ciphertext byte[2] == 0x35

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct = chacha20_encrypt(key, 1, nonce, pt)
expect(ct[2]).to_equal(0x35)
```

</details>

#### ChaCha20 RFC 7539: ciphertext byte[3] == 0x9a

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct = chacha20_encrypt(key, 1, nonce, pt)
expect(ct[3]).to_equal(0x9a)
```

</details>

#### ChaCha20 RFC 7539: ciphertext is not all zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct = chacha20_encrypt(key, 1, nonce, pt)
expect((ct[0] != 0) or (ct[1] != 0) or (ct[2] != 0)).to_equal(true)
```

</details>

#### ChaCha20 different counter produces different output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
var pt: [u8] = [0x4c, 0x61, 0x64, 0x69, 0x65, 0x73, 0x20, 0x61]
val ct0 = chacha20_encrypt(key, 0, nonce, pt)
val ct1 = chacha20_encrypt(key, 1, nonce, pt)
expect(ct0[0] != ct1[0] or ct0[1] != ct1[1]).to_equal(true)
```

</details>

#### ChaCha20 double-encrypt recovers original byte[0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
var pt: [u8] = [0x48, 0x65, 0x6c, 0x6c, 0x6f]
val ct = chacha20_encrypt(key, 1, nonce, pt)
val recovered = chacha20_encrypt(key, 1, nonce, ct)
expect(recovered[0]).to_equal(pt[0])
```

</details>

#### ChaCha20 double-encrypt recovers original byte[1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
var pt: [u8] = [0x48, 0x65, 0x6c, 0x6c, 0x6f]
val ct = chacha20_encrypt(key, 1, nonce, pt)
val recovered = chacha20_encrypt(key, 1, nonce, ct)
expect(recovered[1]).to_equal(pt[1])
```

</details>

#### ChaCha20 double-encrypt recovers original byte[4]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
var pt: [u8] = [0x48, 0x65, 0x6c, 0x6c, 0x6f]
val ct = chacha20_encrypt(key, 1, nonce, pt)
val recovered = chacha20_encrypt(key, 1, nonce, ct)
expect(recovered[4]).to_equal(pt[4])
```

</details>

#### ChaCha20 different keys produce different output

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Inline literals avoid interpreter push-loop array consumption
var key1: [u8] = [
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
]
var key2: [u8] = [
    0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,
    0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,
    0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,
    0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01
]
var nonce: [u8] = [0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]
var pt: [u8] = [0x41, 0x42, 0x43, 0x44]
val ct1 = chacha20_encrypt(key1, 0, nonce, pt)
val ct2 = chacha20_encrypt(key2, 0, nonce, pt)
expect(ct1[0] != ct2[0] or ct1[1] != ct2[1]).to_equal(true)
```

</details>

#### ChaCha20 encrypts empty plaintext to empty ciphertext

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
var pt: [u8] = []
val ct = chacha20_encrypt(key, 1, nonce, pt)
expect(ct.len()).to_equal(0)
```

</details>

### OS Crypto Ref: Poly1305 MAC

#### Poly1305 RFC 7539 §2.5.2: MAC length is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
    0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
    0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
    0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
]
var msg: [u8] = [
    0x43,0x72,0x79,0x70,0x74,0x6f,0x67,0x72,
    0x61,0x70,0x68,0x69,0x63,0x20,0x46,0x6f,
    0x72,0x75,0x6d,0x20,0x52,0x65,0x73,0x65,
    0x61,0x72,0x63,0x68,0x20,0x47,0x72,0x6f,
    0x75,0x70
]
val mac = poly1305_mac(key, msg)
expect(mac.len()).to_equal(16)
```

</details>

#### Poly1305 RFC 7539 §2.5.2: MAC byte[0] == 0xa8

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
    0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
    0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
    0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
]
var msg: [u8] = [
    0x43,0x72,0x79,0x70,0x74,0x6f,0x67,0x72,
    0x61,0x70,0x68,0x69,0x63,0x20,0x46,0x6f,
    0x72,0x75,0x6d,0x20,0x52,0x65,0x73,0x65,
    0x61,0x72,0x63,0x68,0x20,0x47,0x72,0x6f,
    0x75,0x70
]
val mac = poly1305_mac(key, msg)
expect(mac[0]).to_equal(0xa8)
```

</details>

#### Poly1305 RFC 7539 §2.5.2: MAC byte[1] == 0x06

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
    0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
    0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
    0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
]
var msg: [u8] = [
    0x43,0x72,0x79,0x70,0x74,0x6f,0x67,0x72,
    0x61,0x70,0x68,0x69,0x63,0x20,0x46,0x6f,
    0x72,0x75,0x6d,0x20,0x52,0x65,0x73,0x65,
    0x61,0x72,0x63,0x68,0x20,0x47,0x72,0x6f,
    0x75,0x70
]
val mac = poly1305_mac(key, msg)
expect(mac[1]).to_equal(0x06)
```

</details>

#### Poly1305 RFC 7539 §2.5.2: full MAC matches canonical tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
    0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
    0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
    0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
]
var msg: [u8] = [
    0x43,0x72,0x79,0x70,0x74,0x6f,0x67,0x72,
    0x61,0x70,0x68,0x69,0x63,0x20,0x46,0x6f,
    0x72,0x75,0x6d,0x20,0x52,0x65,0x73,0x65,
    0x61,0x72,0x63,0x68,0x20,0x47,0x72,0x6f,
    0x75,0x70
]
val mac = poly1305_mac(key, msg)
expect(bytes_to_hex(mac)).to_equal("a8061dc1305136c6c22b8baf0c0127a9")
```

</details>

#### Poly1305 RFC 7539 §2.5.2: MAC is not all zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
    0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
    0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
    0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
]
var msg: [u8] = [
    0x43,0x72,0x79,0x70,0x74,0x6f,0x67,0x72,
    0x61,0x70,0x68,0x69,0x63,0x20,0x46,0x6f,
    0x72,0x75,0x6d,0x20,0x52,0x65,0x73,0x65,
    0x61,0x72,0x63,0x68,0x20,0x47,0x72,0x6f,
    0x75,0x70
]
val mac = poly1305_mac(key, msg)
expect((mac[0] != 0) or (mac[1] != 0) or (mac[2] != 0)).to_equal(true)
```

</details>

#### Poly1305 different keys produce different MACs

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key1: [u8] = [
    0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
    0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
    0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
    0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
]
# Inline literal avoids interpreter push-loop array consumption
var key2: [u8] = [
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
]
var msg: [u8] = [0x43, 0x72, 0x79, 0x70, 0x74, 0x6f]
val mac1 = poly1305_mac(key1, msg)
val mac2 = poly1305_mac(key2, msg)
expect(mac1[0] != mac2[0] or mac1[1] != mac2[1]).to_equal(true)
```

</details>

#### Poly1305 different messages produce different MACs

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
    0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
    0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
    0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
]
var msg1: [u8] = [0x43, 0x72, 0x79, 0x70]
var msg2: [u8] = [0x43, 0x72, 0x79, 0x71]
val mac1 = poly1305_mac(key, msg1)
val mac2 = poly1305_mac(key, msg2)
expect(mac1[0] != mac2[0] or mac1[1] != mac2[1]).to_equal(true)
```

</details>

#### Poly1305 is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
    0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
    0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
    0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
]
var msg: [u8] = [0x43, 0x72, 0x79, 0x70]
val mac1 = poly1305_mac(key, msg)
val mac2 = poly1305_mac(key, msg)
expect(_bytes_eq(mac1, mac2)).to_equal(true)
```

</details>

### OS Crypto Ref: ChaCha20-Poly1305 AEAD

#### ChaCha20-Poly1305 RFC 7539 §2.8.2: output is plaintext.len + 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7]
val pt = _sunscreen_pt()
val out = chacha20_poly1305_encrypt(key, nonce, pt, aad)
expect(out.len()).to_equal(130)
```

</details>

#### ChaCha20-Poly1305 RFC 7539 §2.8.2: ciphertext byte[0] == 0xd3

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7]
val pt = _sunscreen_pt()
val out = chacha20_poly1305_encrypt(key, nonce, pt, aad)
expect(out[0]).to_equal(0xd3)
```

</details>

#### ChaCha20-Poly1305 RFC 7539 §2.8.2: ciphertext byte[1] == 0x1a

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7]
val pt = _sunscreen_pt()
val out = chacha20_poly1305_encrypt(key, nonce, pt, aad)
expect(out[1]).to_equal(0x1a)
```

</details>

#### ChaCha20-Poly1305 RFC 7539 §2.8.2: ciphertext byte[2] == 0x8d

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7]
val pt = _sunscreen_pt()
val out = chacha20_poly1305_encrypt(key, nonce, pt, aad)
expect(out[2]).to_equal(0x8d)
```

</details>

#### ChaCha20-Poly1305 RFC 7539 §2.8.2: ciphertext byte[3] == 0x34

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7]
val pt = _sunscreen_pt()
val out = chacha20_poly1305_encrypt(key, nonce, pt, aad)
expect(out[3]).to_equal(0x34)
```

</details>

#### ChaCha20-Poly1305 RFC 8439 §2.8.2: full ciphertext and tag match the canonical vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7]
val pt = _sunscreen_pt()
val out = chacha20_poly1305_encrypt(key, nonce, pt, aad)
expect(bytes_to_hex(out)).to_equal(RFC8439_CT_TAG_HEX)
```

</details>

#### ChaCha20-Poly1305 rejects an all-zero tag for the RFC 8439 vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7]
val out = hex_to_bytes(RFC8439_CT_TAG_HEX)
val ciphertext = out.slice(0, out.len() - 16)
val zero_tag = [
    0x00u8,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
]
val dec = chacha20_poly1305_decrypt(key, nonce, ciphertext, aad, zero_tag)
match dec:
    case Chacha20Poly1305Result.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
    case Chacha20Poly1305Result.Ok(data):
        expect(bytes_to_hex(data)).to_equal("unexpected-success")
```

</details>

#### ChaCha20-Poly1305 different keys produce different outputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key1: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
# Inline literal avoids interpreter push-loop array consumption
var key2: [u8] = [
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53]
var pt: [u8] = [0x4c, 0x61, 0x64, 0x69, 0x65, 0x73]
val out1 = chacha20_poly1305_encrypt(key1, nonce, pt, aad)
val out2 = chacha20_poly1305_encrypt(key2, nonce, pt, aad)
expect(out1[0] != out2[0] or out1[1] != out2[1]).to_equal(true)
```

</details>

#### ChaCha20-Poly1305 is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53]
var pt: [u8] = [0x4c, 0x61, 0x64, 0x69, 0x65, 0x73]
val out1 = chacha20_poly1305_encrypt(key, nonce, pt, aad)
val out2 = chacha20_poly1305_encrypt(key, nonce, pt, aad)
expect(_bytes_eq(out1, out2)).to_equal(true)
```

</details>

#### ChaCha20-Poly1305 empty plaintext produces 16-byte tag only

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [u8] = [
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
]
var nonce: [u8] = [0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]
var aad: [u8] = [0x50,0x51,0x52,0x53]
var pt: [u8] = []
val out = chacha20_poly1305_encrypt(key, nonce, pt, aad)
expect(out.len()).to_equal(16)
```

</details>

### OS Crypto Ref: X25519 RFC 7748

#### RFC 7748: x25519_base matches Alice public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = hex_to_bytes(X25519_A_HEX)
val expected = hex_to_bytes(X25519_A_PUBLIC_HEX)
val public_key = x25519_base(a)
expect(_bytes_eq(public_key, expected)).to_equal(true)
```

</details>

#### RFC 7748: x25519 shared secret matches the RFC vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = hex_to_bytes(X25519_A_HEX)
val b_pub = hex_to_bytes(X25519_B_PUBLIC_HEX)
val expected = hex_to_bytes(X25519_SHARED_HEX)
val shared = x25519(a, b_pub)
expect(_bytes_eq(shared, expected)).to_equal(true)
```

</details>

#### RFC 7748: iterative x25519(9, 9) matches the one-step vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = hex_to_bytes(X25519_ITER_HEX)
val u = hex_to_bytes(X25519_ITER_HEX)
val expected = hex_to_bytes(X25519_ITER_ONE_HEX)
val out = x25519(scalar, u)
expect(_bytes_eq(out, expected)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

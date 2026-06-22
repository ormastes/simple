# Aead Specification

> <details>

<!-- sdn-diagram:id=aead_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aead_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aead_spec -> std
aead_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aead_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aead Specification

## Scenarios

### aes256_gcm_seal

#### KAT1: zero-key zero-iv empty-pt empty-aad produces correct tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NIST vector: key=0x00*32, iv=0x00*12, pt=empty, aad=empty
# Expected tag: 530f8afbc74536b9a963b4f1c4cb738b
val key = SecretKey.new(_make_zero_bytes(32))
val nonce = Nonce.new(_make_zero_bytes(12))
val pt = Plaintext.new([])
val aad = ByteSpan.empty()

val sealed = aes256_gcm_seal(key, nonce, pt, aad)
expect(sealed.ct.hex()).to_equal("")
expect(sealed.tag.hex()).to_equal("530f8afbc74536b9a963b4f1c4cb738b")
```

</details>

#### KAT2: zero-key zero-iv 16-zero-byte-pt empty-aad produces correct ct and tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NIST vector: key=0x00*32, iv=0x00*12, pt=0x00*16, aad=empty
# Expected ct: cea7403d4d606b6e074ec5d3baf39d18
# Expected tag: d0d1c8a799996bf0265b98b5d48ab919
val key = SecretKey.new(_make_zero_bytes(32))
val nonce = Nonce.new(_make_zero_bytes(12))
val pt = Plaintext.new(_make_zero_bytes(16))
val aad = ByteSpan.empty()

val sealed = aes256_gcm_seal(key, nonce, pt, aad)
expect(sealed.ct.hex()).to_equal("cea7403d4d606b6e074ec5d3baf39d18")
expect(sealed.tag.hex()).to_equal("d0d1c8a799996bf0265b98b5d48ab919")
```

</details>

#### seal returns typed Ciphertext and AuthTag with correct lengths

- SecretKey new
- Nonce new
- Plaintext new
- ByteSpan empty
   - Expected: sealed.tag.len() equals `16`
   - Expected: sealed.ct.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sealed = aes256_gcm_seal(
    SecretKey.new(_make_zero_bytes(32)),
    Nonce.new(_make_zero_bytes(12)),
    Plaintext.new([]),
    ByteSpan.empty()
)
expect(sealed.tag.len()).to_equal(16)
expect(sealed.ct.len()).to_equal(0)
```

</details>

### aes256_gcm_open

#### KAT1: round-trips empty plaintext through seal then open

- SecretKey new
- Nonce new
   - Expected: inner_pt.hex() equals ``
   - Expected: "open failed: " + inner_msg equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = SecretKey.new(_make_zero_bytes(32))
val nonce = Nonce.new(_make_zero_bytes(12))
val aad = ByteSpan.empty()
val sealed = aes256_gcm_seal(key, nonce, Plaintext.new([]), aad)

val opened = aes256_gcm_open(
    SecretKey.new(_make_zero_bytes(32)),
    Nonce.new(_make_zero_bytes(12)),
    sealed.ct, aad, sealed.tag
)

if val AeadOpenResult.Ok(inner_pt) = opened:
    expect(inner_pt.hex()).to_equal("")
if val AeadOpenResult.Err(inner_msg) = opened:
    expect("open failed: " + inner_msg).to_equal("should have succeeded")
```

</details>

#### KAT2: round-trips 16-byte zero plaintext through seal then open

- SecretKey new
- Nonce new
   - Expected: inner_pt.len() equals `16`
   - Expected: inner_pt.hex() equals `00000000000000000000000000000000`
   - Expected: "open failed: " + inner_msg equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = SecretKey.new(_make_zero_bytes(32))
val nonce = Nonce.new(_make_zero_bytes(12))
val aad = ByteSpan.empty()
val sealed = aes256_gcm_seal(key, nonce, Plaintext.new(_make_zero_bytes(16)), aad)

val opened = aes256_gcm_open(
    SecretKey.new(_make_zero_bytes(32)),
    Nonce.new(_make_zero_bytes(12)),
    sealed.ct, aad, sealed.tag
)

if val AeadOpenResult.Ok(inner_pt) = opened:
    expect(inner_pt.len()).to_equal(16)
    expect(inner_pt.hex()).to_equal("00000000000000000000000000000000")
if val AeadOpenResult.Err(inner_msg) = opened:
    expect("open failed: " + inner_msg).to_equal("should have succeeded")
```

</details>

#### open returns Err on tampered tag (fail-closed)

- SecretKey new
- Nonce new
- Plaintext new
- ByteSpan empty
- SecretKey new
- Nonce new
- sealed ct, ByteSpan empty
   - Expected: "tampered tag accepted" equals `should have returned Err`
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sealed = aes256_gcm_seal(
    SecretKey.new(_make_zero_bytes(32)),
    Nonce.new(_make_zero_bytes(12)),
    Plaintext.new(_make_zero_bytes(16)),
    ByteSpan.empty()
)
val opened = aes256_gcm_open(
    SecretKey.new(_make_zero_bytes(32)),
    Nonce.new(_make_zero_bytes(12)),
    sealed.ct, ByteSpan.empty(), AuthTag.new(_bad_tag())
)

if val AeadOpenResult.Ok(inner_pt) = opened:
    expect("tampered tag accepted").to_equal("should have returned Err")
if val AeadOpenResult.Err(inner_msg) = opened:
    expect(true).to_equal(true)
```

</details>

#### open returns Err on tampered ciphertext (fail-closed)

- SecretKey new
- Nonce new
- Plaintext new
- ByteSpan empty
- SecretKey new
- Nonce new
- bad ct, ByteSpan empty
   - Expected: "tampered ct accepted" equals `should have returned Err`
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sealed = aes256_gcm_seal(
    SecretKey.new(_make_zero_bytes(32)),
    Nonce.new(_make_zero_bytes(12)),
    Plaintext.new(_make_zero_bytes(16)),
    ByteSpan.empty()
)
val bad_ct = Ciphertext.new(_bad_tag())
val opened = aes256_gcm_open(
    SecretKey.new(_make_zero_bytes(32)),
    Nonce.new(_make_zero_bytes(12)),
    bad_ct, ByteSpan.empty(), sealed.tag
)

if val AeadOpenResult.Ok(inner_pt) = opened:
    expect("tampered ct accepted").to_equal("should have returned Err")
if val AeadOpenResult.Err(inner_msg) = opened:
    expect(true).to_equal(true)
```

</details>

### chacha20_poly1305_seal

#### RFC8439-§2.8.2: produces correct Poly1305 tag

- SecretKey new
- Nonce new
- Plaintext new
- ByteSpan new
   - Expected: sealed.tag.hex() equals `1ae10b594f09e26a7e902ecbd0600691`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sealed = chacha20_poly1305_seal(
    SecretKey.new(_make_cc_key()),
    Nonce.new(_make_cc_nonce()),
    Plaintext.new(_make_cc_pt()),
    ByteSpan.new(_make_cc_aad())
)
# RFC 8439 §2.8.2 absolute oracle
expect(sealed.tag.hex()).to_equal("1ae10b594f09e26a7e902ecbd0600691")
```

</details>

#### RFC8439-§2.8.2: ciphertext starts with correct 8-byte prefix

- SecretKey new
- Nonce new
- Plaintext new
- ByteSpan new
   - Expected: prefix equals `d31a8d34648e60db`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sealed = chacha20_poly1305_seal(
    SecretKey.new(_make_cc_key()),
    Nonce.new(_make_cc_nonce()),
    Plaintext.new(_make_cc_pt()),
    ByteSpan.new(_make_cc_aad())
)
# RFC 8439 §2.8.2: first 8 bytes of ct hex = d31a8d34648e60db
val ct_hex = sealed.ct.hex()
val prefix = ct_hex.slice(0, 16)
expect(prefix).to_equal("d31a8d34648e60db")
```

</details>

#### seal returns Ciphertext and AuthTag with correct sizes

- SecretKey new
- Nonce new
- Plaintext new
- ByteSpan empty
   - Expected: sealed.tag.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sealed = chacha20_poly1305_seal(
    SecretKey.new(_make_cc_key()),
    Nonce.new(_make_cc_nonce()),
    Plaintext.new([]),
    ByteSpan.empty()
)
expect(sealed.tag.len()).to_equal(16)
```

</details>

### chacha20_poly1305_open

#### round-trips RFC8439 plaintext through seal then open

- SecretKey new
- Nonce new
- Plaintext new
- ByteSpan new
- SecretKey new
- Nonce new
- ByteSpan new
   - Expected: inner_pt.hex() equals `4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f6620273... (full value in folded executable source)`
   - Expected: "open failed: " + inner_msg equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cc_pt_b = _make_cc_pt()
val sealed = chacha20_poly1305_seal(
    SecretKey.new(_make_cc_key()),
    Nonce.new(_make_cc_nonce()),
    Plaintext.new(cc_pt_b),
    ByteSpan.new(_make_cc_aad())
)
val opened = chacha20_poly1305_open(
    SecretKey.new(_make_cc_key()),
    Nonce.new(_make_cc_nonce()),
    sealed.ct,
    ByteSpan.new(_make_cc_aad()),
    sealed.tag
)

if val AeadOpenResult.Ok(inner_pt) = opened:
    expect(inner_pt.hex()).to_equal("4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e")
if val AeadOpenResult.Err(inner_msg) = opened:
    expect("open failed: " + inner_msg).to_equal("should have succeeded")
```

</details>

#### open returns Err on tampered tag (fail-closed)

- var small pt: [u8] = "test" bytes
- SecretKey new
- Nonce new
- Plaintext new
- ByteSpan empty
- SecretKey new
- Nonce new
- sealed ct, ByteSpan empty
   - Expected: "tampered tag accepted" equals `should have returned Err`
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var small_pt: [u8] = "test".bytes()
val sealed = chacha20_poly1305_seal(
    SecretKey.new(_make_cc_key()),
    Nonce.new(_make_cc_nonce()),
    Plaintext.new(small_pt),
    ByteSpan.empty()
)
val opened = chacha20_poly1305_open(
    SecretKey.new(_make_cc_key()),
    Nonce.new(_make_cc_nonce()),
    sealed.ct, ByteSpan.empty(), AuthTag.new(_bad_tag())
)

if val AeadOpenResult.Ok(inner_pt) = opened:
    expect("tampered tag accepted").to_equal("should have returned Err")
if val AeadOpenResult.Err(inner_msg) = opened:
    expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/typed/aead_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- aes256_gcm_seal
- aes256_gcm_open
- chacha20_poly1305_seal
- chacha20_poly1305_open

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

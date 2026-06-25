# ChaCha20-Poly1305 Cross-Vendor Roundtrip Specification

> Intensive byte-level cross-validation of the pure-Simple ChaCha20-Poly1305 AEAD implementation (src/os/crypto/chacha20_poly1305.spl) against reference implementation Node.js `node:crypto`.

<!-- sdn-diagram:id=chacha_poly_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chacha_poly_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chacha_poly_roundtrip_spec -> std
chacha_poly_roundtrip_spec -> os
chacha_poly_roundtrip_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chacha_poly_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ChaCha20-Poly1305 Cross-Vendor Roundtrip Specification

Intensive byte-level cross-validation of the pure-Simple ChaCha20-Poly1305 AEAD implementation (src/os/crypto/chacha20_poly1305.spl) against reference implementation Node.js `node:crypto`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Testing |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/pure_simple_crypto_tls_remains_2026-04-16.md |
| Design | N/A |
| Research | doc/01_research/local/tls13_phase2_backlog.md |
| Source | `test/03_system/security/chacha_poly_roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Intensive byte-level cross-validation of the pure-Simple ChaCha20-Poly1305
AEAD implementation (src/os/crypto/chacha20_poly1305.spl) against reference
implementation Node.js `node:crypto`.

Four interop lanes per test:

1. **Simple-encrypt / Simple-decrypt** — sanity roundtrip.
2. **Simple-encrypt / vendor-decrypt** — our bytes survive external verification.
3. **Vendor-encrypt / Simple-decrypt** — we accept and decrypt external bytes.
4. **Vendor-encrypt / vendor-decrypt** — baseline external reference check.

Plus:
- RFC 8439 §2.8.2 known-answer vector (byte-exact ciphertext + tag).
- Tampered-tag negative path on both vendor and pure-Simple decrypt.

## Out of Scope

Existing-client ↔ Simple-server TLS interop: blocked until server-side TLS 1.3
lands (see doc/01_research/local/tls13_phase2_backlog.md §Server-side TLS 1.3).

## Scenarios

### chacha_poly: RFC 8439 §2.8.2 known-answer

#### node encrypt matches the canonical ciphertext||tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key   = hex_to_bytes(RFC8439_KEY_HEX)
val nonce = hex_to_bytes(RFC8439_NONCE_HEX)
val aad   = hex_to_bytes(RFC8439_AAD_HEX)
val plain = hex_to_bytes(RFC8439_PT_HEX)
val got   = _unwrap_bytes(ref_chacha_poly_encrypt_via(Vendor.NODE, key, nonce, aad, plain))
expect(bytes_to_hex(got)).to_equal(RFC8439_CT_TAG_HEX)
```

</details>

### chacha_poly: Simple ↔ Simple roundtrip over 8-input matrix

<details>
<summary>Advanced: every matrix input round-trips through pure-Simple encrypt+decrypt</summary>

#### every matrix input round-trips through pure-Simple encrypt+decrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key   = hex_to_bytes(RFC8439_KEY_HEX)
val nonce = hex_to_bytes(RFC8439_NONCE_HEX)
val aad   = hex_to_bytes(RFC8439_AAD_HEX)
# ChaCha20 block size = 64 bytes
val matrix = crypto_input_matrix(block_size: 64u64)
var i: u64 = 0
while i < matrix.len():
    val plain    = matrix[i]
    val ct_tag   = chacha20_poly1305_encrypt(key, nonce, plain, aad)
    val split    = _split_ct_tag(ct_tag)
    val recovered = _decrypt_ok_bytes(key, nonce, split.0, aad, split.1)
    expect(_bytes_eq(recovered, plain)).to_equal(true)
    i = i + 1
```

</details>


</details>

### chacha_poly: Simple-encrypt → vendor-decrypt

<details>
<summary>Advanced: node decrypts every pure-Simple-encrypted matrix entry without auth error</summary>

#### node decrypts every pure-Simple-encrypted matrix entry without auth error

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key   = hex_to_bytes(RFC8439_KEY_HEX)
val nonce = hex_to_bytes(RFC8439_NONCE_HEX)
val aad   = hex_to_bytes(RFC8439_AAD_HEX)
val matrix = crypto_input_matrix(block_size: 64u64)
var i: u64 = 0
while i < matrix.len():
    val plain    = matrix[i]
    val ct_tag   = chacha20_poly1305_encrypt(key, nonce, plain, aad)
    val result   = ref_chacha_poly_decrypt_via(Vendor.NODE, key, nonce, aad, ct_tag)
    expect(_is_err(result)).to_equal(false)
    val recovered = _unwrap_bytes(result)
    expect(_bytes_eq(recovered, plain)).to_equal(true)
    i = i + 1
```

</details>


</details>

### chacha_poly: vendor-encrypt → Simple-decrypt

<details>
<summary>Advanced: pure-Simple decrypts every node-encrypted matrix entry</summary>

#### pure-Simple decrypts every node-encrypted matrix entry

1. ref chacha poly encrypt via
   - Expected: _bytes_eq(recovered, plain) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key   = hex_to_bytes(RFC8439_KEY_HEX)
val nonce = hex_to_bytes(RFC8439_NONCE_HEX)
val aad   = hex_to_bytes(RFC8439_AAD_HEX)
val matrix = crypto_input_matrix(block_size: 64u64)
var i: u64 = 0
while i < matrix.len():
    val plain = matrix[i]
    val ct_tag = _unwrap_bytes(
        ref_chacha_poly_encrypt_via(Vendor.NODE, key, nonce, aad, plain))
    val split = _split_ct_tag(ct_tag)
    val recovered = _decrypt_ok_bytes(key, nonce, split.0, aad, split.1)
    expect(_bytes_eq(recovered, plain)).to_equal(true)
    i = i + 1
```

</details>


</details>

### chacha_poly: vendor ↔ vendor roundtrip

<details>
<summary>Advanced: node-encrypt → node-decrypt recovers every matrix entry</summary>

#### node-encrypt → node-decrypt recovers every matrix entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key   = hex_to_bytes(RFC8439_KEY_HEX)
val nonce = hex_to_bytes(RFC8439_NONCE_HEX)
val aad   = hex_to_bytes(RFC8439_AAD_HEX)
val matrix = crypto_input_matrix(block_size: 64u64)
var i: u64 = 0
while i < matrix.len():
    val plain  = matrix[i]
    val ct_tag = _unwrap_bytes(ref_chacha_poly_encrypt_via(Vendor.NODE, key, nonce, aad, plain))
    val got    = _unwrap_bytes(ref_chacha_poly_decrypt_via(Vendor.NODE, key, nonce, aad, ct_tag))
    expect(_bytes_eq(got, plain)).to_equal(true)
    i = i + 1
```

</details>


</details>

### chacha_poly: tampered-tag authentication failure

#### node decrypt rejects the same tampered ciphertext||tag

1. tampered push
2. tampered push
   - Expected: _is_err(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key   = hex_to_bytes(RFC8439_KEY_HEX)
val nonce = hex_to_bytes(RFC8439_NONCE_HEX)
val aad   = hex_to_bytes(RFC8439_AAD_HEX)
val plain = hex_to_bytes(RFC8439_PT_HEX)
val ct_tag = chacha20_poly1305_encrypt(key, nonce, plain, aad)
var tampered: [u8] = []
var i: u64 = 0
while i < ct_tag.len() - 1:
    tampered.push(ct_tag[i])
    i = i + 1
tampered.push((ct_tag[ct_tag.len() - 1].to_i64() ^ 0xff).to_u8())
val r = ref_chacha_poly_decrypt_via(Vendor.NODE, key, nonce, aad, tampered)
expect(_is_err(r)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/pure_simple_crypto_tls_remains_2026-04-16.md](doc/03_plan/agent_tasks/pure_simple_crypto_tls_remains_2026-04-16.md)
- **Research:** [doc/01_research/local/tls13_phase2_backlog.md](doc/01_research/local/tls13_phase2_backlog.md)


</details>

# ChaCha20-Poly1305 Cross-Vendor Roundtrip Specification

> Intensive byte-level cross-validation of the pure-Simple ChaCha20-Poly1305 AEAD implementation (src/os/crypto/chacha20_poly1305.spl) against reference implementation Node.js `node:crypto`.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- node encrypt matches the canonical ciphertext||tag
   - Expected: bytes_to_hex(got) equals `RFC8439_CT_TAG_HEX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node encrypt matches the canonical ciphertext||tag")
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

- every matrix input round-trips through pure-Simple encrypt+decrypt
   - Expected: _bytes_eq(recovered, plain) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("every matrix input round-trips through pure-Simple encrypt+decrypt")
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

- node decrypts every pure-Simple-encrypted matrix entry without auth error
   - Expected: _is_err(result) is false
   - Expected: _bytes_eq(recovered, plain) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node decrypts every pure-Simple-encrypted matrix entry without auth error")
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

- pure-Simple decrypts every node-encrypted matrix entry
   - Expected: _bytes_eq(recovered, plain) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pure-Simple decrypts every node-encrypted matrix entry")
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

- node-encrypt → node-decrypt recovers every matrix entry
   - Expected: _bytes_eq(got, plain) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node-encrypt → node-decrypt recovers every matrix entry")
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

- node decrypt rejects the same tampered ciphertext||tag
   - Expected: _is_err(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node decrypt rejects the same tampered ciphertext||tag")
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

- **Plan:** `doc/03_plan/agent_tasks/pure_simple_crypto_tls_remains_2026-04-16.md`
- **Research:** `doc/01_research/local/tls13_phase2_backlog.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b66c669c49c3d98339a06ad09f692db4b63fc34b9e908b714f63323aea52878`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b66c669c49c3d98339a06ad09f692db4b63fc34b9e908b714f63323aea52878`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b66c669c49c3d98339a06ad09f692db4b63fc34b9e908b714f63323aea52878`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/security/chacha_poly_roundtrip_spec.spl
mirror: doc/06_spec/03_system/security/chacha_poly_roundtrip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/security/chacha_poly_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/chacha_poly_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/chacha_poly_roundtrip_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'node encrypt matches the canonical ciphertext||tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/chacha_poly_roundtrip_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every matrix input round-trips through pure-Simple encrypt+decrypt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/chacha_poly_roundtrip_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'node decrypts every pure-Simple-encrypted matrix entry without auth error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

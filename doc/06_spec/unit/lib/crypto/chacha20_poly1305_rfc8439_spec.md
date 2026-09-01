# Chacha20 Poly1305 Rfc8439 Specification

> Tests covering ChaCha20-Poly1305 RFC 8439 §2.4.2 stream ciphertext via AEAD wrapper, ChaCha20-Poly1305 RFC 8439 §2.8.2 canonical AEAD vector, ChaCha20-Poly1305 RFC 8439 A.5 #5 (256-byte input, 4 ChaCha blocks).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Poly1305 Rfc8439 Specification

## Scenarios

### ChaCha20-Poly1305 RFC 8439 §2.4.2 stream ciphertext via AEAD wrapper

#### encrypt produces canonical §2.4.2 ciphertext bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encrypt produces canonical §2.4.2 ciphertext bytes
   - Expected: _bytes_eq(split.0, EXPECTED_CT_2_4_2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt produces canonical §2.4.2 ciphertext bytes")
val combined = chacha20_poly1305_encrypt(KEY_2_4_2, NONCE_2_4_2, PT_2_4_2, AAD_EMPTY)
val split = _split_ct_tag(combined)
expect(_bytes_eq(split.0, EXPECTED_CT_2_4_2)).to_equal(true)
```

</details>

#### output length is plaintext length + 16 (tag)

- output length is plaintext length + 16 (tag)
   - Expected: combined.len() equals `130u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output length is plaintext length + 16 (tag)")
val combined = chacha20_poly1305_encrypt(KEY_2_4_2, NONCE_2_4_2, PT_2_4_2, AAD_EMPTY)
expect(combined.len()).to_equal(130u64)
```

</details>

### ChaCha20-Poly1305 RFC 8439 §2.8.2 canonical AEAD vector

#### encrypts plaintext to expected ciphertext

- encrypts plaintext to expected ciphertext
   - Expected: _bytes_eq(split.0, EXPECTED_CT_2_8_2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts plaintext to expected ciphertext")
val combined = chacha20_poly1305_encrypt(KEY_2_8_2, NONCE_2_8_2, PT_2_8_2, AAD_2_8_2)
val split = _split_ct_tag(combined)
expect(_bytes_eq(split.0, EXPECTED_CT_2_8_2)).to_equal(true)
```

</details>

#### encrypts to expected Poly1305 tag

- encrypts to expected Poly1305 tag
   - Expected: _bytes_eq(split.1, EXPECTED_TAG_2_8_2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts to expected Poly1305 tag")
# Known-failing: impl tag diverges from canonical for 114-byte inputs.
# See doc/01_research/local/chacha_poly_tag_bug_2026-04-17.md
val combined = chacha20_poly1305_encrypt(KEY_2_8_2, NONCE_2_8_2, PT_2_8_2, AAD_2_8_2)
val split = _split_ct_tag(combined)
expect(_bytes_eq(split.1, EXPECTED_TAG_2_8_2)).to_equal(true)
```

</details>

#### decrypts canonical ciphertext+tag back to plaintext

- decrypts canonical ciphertext+tag back to plaintext
   - Expected: _bytes_eq(pt, PT_2_8_2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts canonical ciphertext+tag back to plaintext")
val pt = _decrypt_ok(KEY_2_8_2, NONCE_2_8_2, EXPECTED_CT_2_8_2, AAD_2_8_2, EXPECTED_TAG_2_8_2)
expect(_bytes_eq(pt, PT_2_8_2)).to_equal(true)
```

</details>

#### rejects a one-bit-flipped tag

- rejects a one-bit-flipped tag
   - Expected: _decrypt_is_err(KEY_2_8_2, NONCE_2_8_2, EXPECTED_CT_2_8_2, AAD_2_8_2, bad_tag) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a one-bit-flipped tag")
val bad_tag = _corrupt(EXPECTED_TAG_2_8_2, 0u64)
expect(_decrypt_is_err(KEY_2_8_2, NONCE_2_8_2, EXPECTED_CT_2_8_2, AAD_2_8_2, bad_tag)).to_equal(true)
```

</details>

#### rejects corrupted AAD

- rejects corrupted AAD
   - Expected: _decrypt_is_err(KEY_2_8_2, NONCE_2_8_2, EXPECTED_CT_2_8_2, bad_aad, EXPECTED_TAG_2_8_2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects corrupted AAD")
val bad_aad = _corrupt(AAD_2_8_2, 0u64)
expect(_decrypt_is_err(KEY_2_8_2, NONCE_2_8_2, EXPECTED_CT_2_8_2, bad_aad, EXPECTED_TAG_2_8_2)).to_equal(true)
```

</details>

#### rejects corrupted ciphertext

- rejects corrupted ciphertext
   - Expected: _decrypt_is_err(KEY_2_8_2, NONCE_2_8_2, bad_ct, AAD_2_8_2, EXPECTED_TAG_2_8_2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects corrupted ciphertext")
val bad_ct = _corrupt(EXPECTED_CT_2_8_2, 0u64)
expect(_decrypt_is_err(KEY_2_8_2, NONCE_2_8_2, bad_ct, AAD_2_8_2, EXPECTED_TAG_2_8_2)).to_equal(true)
```

</details>

### ChaCha20-Poly1305 RFC 8439 A.5 #5 (256-byte input, 4 ChaCha blocks)

#### output length is plaintext length + 16 (tag)

- output length is plaintext length + 16 (tag)
   - Expected: combined.len() equals `272u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output length is plaintext length + 16 (tag)")
val combined = chacha20_poly1305_encrypt(KEY_A5_5, NONCE_A5_5, PT_A5_5, AAD_A5_5)
expect(combined.len()).to_equal(272u64)
```

</details>

#### roundtrip: decrypt recovers original plaintext

- roundtrip: decrypt recovers original plaintext
   - Expected: _bytes_eq(recovered, PT_A5_5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrip: decrypt recovers original plaintext")
val combined = chacha20_poly1305_encrypt(KEY_A5_5, NONCE_A5_5, PT_A5_5, AAD_A5_5)
val split = _split_ct_tag(combined)
val recovered = _decrypt_ok(KEY_A5_5, NONCE_A5_5, split.0, AAD_A5_5, split.1)
expect(_bytes_eq(recovered, PT_A5_5)).to_equal(true)
```

</details>

#### rejects a one-bit-flipped tag

- rejects a one-bit-flipped tag
   - Expected: _decrypt_is_err(KEY_A5_5, NONCE_A5_5, split.0, AAD_A5_5, bad_tag) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a one-bit-flipped tag")
val combined = chacha20_poly1305_encrypt(KEY_A5_5, NONCE_A5_5, PT_A5_5, AAD_A5_5)
val split = _split_ct_tag(combined)
val bad_tag = _corrupt(split.1, 0u64)
expect(_decrypt_is_err(KEY_A5_5, NONCE_A5_5, split.0, AAD_A5_5, bad_tag)).to_equal(true)
```

</details>

#### rejects corrupted AAD

- rejects corrupted AAD
   - Expected: _decrypt_is_err(KEY_A5_5, NONCE_A5_5, split.0, bad_aad, split.1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects corrupted AAD")
val combined = chacha20_poly1305_encrypt(KEY_A5_5, NONCE_A5_5, PT_A5_5, AAD_A5_5)
val split = _split_ct_tag(combined)
val bad_aad = _corrupt(AAD_A5_5, 0u64)
expect(_decrypt_is_err(KEY_A5_5, NONCE_A5_5, split.0, bad_aad, split.1)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ChaCha20-Poly1305 RFC 8439 §2.4.2 stream ciphertext via AEAD wrapper, ChaCha20-Poly1305 RFC 8439 §2.8.2 canonical AEAD vector, ChaCha20-Poly1305 RFC 8439 A.5 #5 (256-byte input, 4 ChaCha blocks).
- ChaCha20-Poly1305 RFC 8439 §2.4.2 stream ciphertext via AEAD wrapper
- ChaCha20-Poly1305 RFC 8439 §2.8.2 canonical AEAD vector
- ChaCha20-Poly1305 RFC 8439 A.5 #5 (256-byte input, 4 ChaCha blocks)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `63ec7fee6e17de1281f51e8c68106ce45d19d09ec58212e8e651ac9fb3de4900`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63ec7fee6e17de1281f51e8c68106ce45d19d09ec58212e8e651ac9fb3de4900`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63ec7fee6e17de1281f51e8c68106ce45d19d09ec58212e8e651ac9fb3de4900`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.spl
mirror: doc/06_spec/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.spl:282:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encrypt produces canonical §2.4.2 ciphertext bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.spl:289:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'output length is plaintext length + 16 (tag)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.spl:301:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encrypts plaintext to expected ciphertext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

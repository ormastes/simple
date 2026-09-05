# Chacha20 Poly1305 Specification

> Tests covering ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — ciphertext, ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — tag, ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — round-trip, ChaCha20-Poly1305 stdlib — authentication failure, ChaCha20-Poly1305 stdlib — empty AAD, ChaCha20-Poly1305 stdlib — empty plaintext.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Poly1305 Specification

## Scenarios

### ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — ciphertext

#### seal produces canonical §2.8.2 ciphertext byte-exact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- seal produces canonical §2.8.2 ciphertext byte-exact
   - Expected: _bytes_eq(ct, _expected_ct_2_8_2()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seal produces canonical §2.8.2 ciphertext byte-exact")
val (ct, _tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(_bytes_eq(ct, _expected_ct_2_8_2())).to_equal(true)
```

</details>

#### ciphertext length equals plaintext length (114 bytes)

- ciphertext length equals plaintext length (114 bytes)
   - Expected: ct.len() equals `114u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ciphertext length equals plaintext length (114 bytes)")
val (ct, _tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(ct.len()).to_equal(114u64)
```

</details>

### ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — tag

#### seal produces canonical §2.8.2 Poly1305 tag byte-exact

- seal produces canonical §2.8.2 Poly1305 tag byte-exact
   - Expected: _bytes_eq(tag, _expected_tag_2_8_2()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seal produces canonical §2.8.2 Poly1305 tag byte-exact")
val (_ct, tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(_bytes_eq(tag, _expected_tag_2_8_2())).to_equal(true)
```

</details>

#### tag length is always 16 bytes

- tag length is always 16 bytes
   - Expected: tag.len() equals `16u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tag length is always 16 bytes")
val (_ct, tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(tag.len()).to_equal(16u64)
```

</details>

### ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — round-trip

#### open(seal(pt)) recovers original plaintext

- open(seal(pt)) recovers original plaintext
   - Expected: _open_eq(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), ct, tag, _pt_2_8_2()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("open(seal(pt)) recovers original plaintext")
val (ct, tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
expect(_open_eq(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), ct, tag, _pt_2_8_2())).to_equal(true)
```

</details>

#### open with canonical ct+tag recovers plaintext

- open with canonical ct+tag recovers plaintext


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("open with canonical ct+tag recovers plaintext")
expect(_open_eq(
    _key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(),
    _expected_ct_2_8_2(), _expected_tag_2_8_2(),
    _pt_2_8_2())).to_equal(true)
```

</details>

### ChaCha20-Poly1305 stdlib — authentication failure

#### tampered ciphertext (byte 0 flipped) causes open to return nil

- tampered ciphertext (byte 0 flipped) causes open to return nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tampered ciphertext (byte 0 flipped) causes open to return nil")
val bad_ct = _corrupt(_expected_ct_2_8_2(), 0u64)
expect(_open_is_nil(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(),
    bad_ct, _expected_tag_2_8_2())).to_equal(true)
```

</details>

#### tampered AAD (byte 0 flipped) causes open to return nil

- tampered AAD (byte 0 flipped) causes open to return nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tampered AAD (byte 0 flipped) causes open to return nil")
val bad_aad = _corrupt(_aad_2_8_2(), 0u64)
expect(_open_is_nil(_key_2_8_2(), _nonce_2_8_2(), bad_aad,
    _expected_ct_2_8_2(), _expected_tag_2_8_2())).to_equal(true)
```

</details>

#### tampered tag (byte 0 flipped) causes open to return nil

- tampered tag (byte 0 flipped) causes open to return nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tampered tag (byte 0 flipped) causes open to return nil")
val bad_tag = _corrupt(_expected_tag_2_8_2(), 0u64)
expect(_open_is_nil(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(),
    _expected_ct_2_8_2(), bad_tag)).to_equal(true)
```

</details>

### ChaCha20-Poly1305 stdlib — empty AAD

#### seal with empty AAD produces correct ciphertext length

- seal with empty AAD produces correct ciphertext length
   - Expected: ct.len() equals `114u64`
   - Expected: tag.len() equals `16u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seal with empty AAD produces correct ciphertext length")
val empty_aad: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(
    _key_2_8_2(), _nonce_2_8_2(), empty_aad, _pt_2_8_2())
expect(ct.len()).to_equal(114u64)
expect(tag.len()).to_equal(16u64)
```

</details>

#### round-trip with empty AAD recovers plaintext

- round-trip with empty AAD recovers plaintext
   - Expected: _open_eq(_key_2_8_2(), _nonce_2_8_2(), empty_aad, ct, tag, _pt_2_8_2()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip with empty AAD recovers plaintext")
val empty_aad: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(
    _key_2_8_2(), _nonce_2_8_2(), empty_aad, _pt_2_8_2())
expect(_open_eq(_key_2_8_2(), _nonce_2_8_2(), empty_aad, ct, tag, _pt_2_8_2())).to_equal(true)
```

</details>

### ChaCha20-Poly1305 stdlib — empty plaintext

#### seal with empty plaintext produces empty ciphertext and 16-byte tag

- seal with empty plaintext produces empty ciphertext and 16-byte tag
   - Expected: ct.len() equals `0u64`
   - Expected: tag.len() equals `16u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seal with empty plaintext produces empty ciphertext and 16-byte tag")
val empty_pt: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(
    _key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), empty_pt)
expect(ct.len()).to_equal(0u64)
expect(tag.len()).to_equal(16u64)
```

</details>

#### round-trip with empty plaintext recovers empty plaintext

- round-trip with empty plaintext recovers empty plaintext
   - Expected: _open_len(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), ct, tag) equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip with empty plaintext recovers empty plaintext")
val empty_pt: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(
    _key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), empty_pt)
expect(_open_len(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), ct, tag)).to_equal(0u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/chacha20_poly1305_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — ciphertext, ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — tag, ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — round-trip, ChaCha20-Poly1305 stdlib — authentication failure, ChaCha20-Poly1305 stdlib — empty AAD, ChaCha20-Poly1305 stdlib — empty plaintext.
- ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — ciphertext
- ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — tag
- ChaCha20-Poly1305 stdlib RFC 7539 §2.8.2 — round-trip
- ChaCha20-Poly1305 stdlib — authentication failure
- ChaCha20-Poly1305 stdlib — empty AAD
- ChaCha20-Poly1305 stdlib — empty plaintext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `ed7ed0bdd0b5a21a113aba3608cd955f94c4d935711f8d6e2cca1939531fdbc6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed7ed0bdd0b5a21a113aba3608cd955f94c4d935711f8d6e2cca1939531fdbc6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed7ed0bdd0b5a21a113aba3608cd955f94c4d935711f8d6e2cca1939531fdbc6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/chacha20_poly1305_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/chacha20_poly1305_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/chacha20_poly1305_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/chacha20_poly1305_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/chacha20_poly1305_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seal produces canonical §2.8.2 ciphertext byte-exact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/chacha20_poly1305_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ciphertext length equals plaintext length (114 bytes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/chacha20_poly1305_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seal produces canonical §2.8.2 Poly1305 tag byte-exact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

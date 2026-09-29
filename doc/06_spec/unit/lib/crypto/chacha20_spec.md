# Chacha20 Specification

> Tests covering ChaCha20 RFC 7539 §2.1.1 — quarter-round test vector, ChaCha20 RFC 7539 §2.3.2 — block function test vector, ChaCha20 RFC 7539 §2.4.2 — stream encryption test vector, ChaCha20 — negative tests (wrong key / nonce / counter change output).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Specification

## Scenarios

### ChaCha20 RFC 7539 §2.1.1 — quarter-round test vector

#### produces correct a after quarter-round

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces correct a after quarter-round
   - Expected: result[0] equals `0xea2a92f4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct a after quarter-round")
val result = _qr_test_vector()
expect(result[0]).to_equal(0xea2a92f4u32)
```

</details>

#### produces correct b after quarter-round

- produces correct b after quarter-round
   - Expected: result[1] equals `0xcb1cf8ceu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct b after quarter-round")
val result = _qr_test_vector()
expect(result[1]).to_equal(0xcb1cf8ceu32)
```

</details>

#### produces correct c after quarter-round

- produces correct c after quarter-round
   - Expected: result[2] equals `0x4581472eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct c after quarter-round")
val result = _qr_test_vector()
expect(result[2]).to_equal(0x4581472eu32)
```

</details>

#### produces correct d after quarter-round

- produces correct d after quarter-round
   - Expected: result[3] equals `0x5881c4bbu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct d after quarter-round")
val result = _qr_test_vector()
expect(result[3]).to_equal(0x5881c4bbu32)
```

</details>

### ChaCha20 RFC 7539 §2.3.2 — block function test vector

#### block output is 64 bytes

- block output is 64 bytes
   - Expected: block.len() equals `16u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block output is 64 bytes")
val block = chacha20_block(_key_words_2_3_2(), 1u32, _nonce_words_2_3_2())
expect(block.len()).to_equal(16u64)
```

</details>

#### block bytes match RFC 7539 §2.3.2 exactly

- block bytes match RFC 7539 §2.3.2 exactly
   - Expected: _bytes_eq(got, _expected_block_2_3_2()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block bytes match RFC 7539 §2.3.2 exactly")
val block = chacha20_block(_key_words_2_3_2(), 1u32, _nonce_words_2_3_2())
val got = _block_to_bytes(block)
expect(_bytes_eq(got, _expected_block_2_3_2())).to_equal(true)
```

</details>

### ChaCha20 RFC 7539 §2.4.2 — stream encryption test vector

#### ciphertext length matches plaintext length

- ciphertext length matches plaintext length
   - Expected: ct.len() equals `114u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ciphertext length matches plaintext length")
val ct = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
expect(ct.len()).to_equal(114u64)
```

</details>

#### ciphertext matches RFC 7539 §2.4.2 expected bytes exactly

- ciphertext matches RFC 7539 §2.4.2 expected bytes exactly
   - Expected: _bytes_eq(ct, _expected_ct_2_4_2()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ciphertext matches RFC 7539 §2.4.2 expected bytes exactly")
val ct = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
expect(_bytes_eq(ct, _expected_ct_2_4_2())).to_equal(true)
```

</details>

#### decryption recovers original plaintext

- decryption recovers original plaintext
   - Expected: _bytes_eq(pt2, _pt_2_4_2()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decryption recovers original plaintext")
val ct = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
val pt2 = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), ct)
expect(_bytes_eq(pt2, _pt_2_4_2())).to_equal(true)
```

</details>

### ChaCha20 — negative tests (wrong key / nonce / counter change output)

#### wrong key produces different ciphertext

- wrong key produces different ciphertext
   - Expected: _bytes_eq(ct_good, ct_bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong key produces different ciphertext")
val ct_good = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
# Flip bit 0 of key byte 0
val bad_key = [0x01u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8,
               0x08u8, 0x09u8, 0x0au8, 0x0bu8, 0x0cu8, 0x0du8, 0x0eu8, 0x0fu8,
               0x10u8, 0x11u8, 0x12u8, 0x13u8, 0x14u8, 0x15u8, 0x16u8, 0x17u8,
               0x18u8, 0x19u8, 0x1au8, 0x1bu8, 0x1cu8, 0x1du8, 0x1eu8, 0x1fu8]
val ct_bad = chacha20_encrypt(bad_key, 1u32, _nonce_2_4_2(), _pt_2_4_2())
expect(_bytes_eq(ct_good, ct_bad)).to_equal(false)
```

</details>

#### wrong nonce produces different ciphertext

- wrong nonce produces different ciphertext
   - Expected: _bytes_eq(ct_good, ct_bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong nonce produces different ciphertext")
val ct_good = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
val bad_nonce = [0x01u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x4au8,
                 0x00u8, 0x00u8, 0x00u8, 0x00u8]
val ct_bad = chacha20_encrypt(_key_2_4_2(), 1u32, bad_nonce, _pt_2_4_2())
expect(_bytes_eq(ct_good, ct_bad)).to_equal(false)
```

</details>

#### wrong counter produces different ciphertext

- wrong counter produces different ciphertext
   - Expected: _bytes_eq(ct_good, ct_bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong counter produces different ciphertext")
val ct_good = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
val ct_bad  = chacha20_encrypt(_key_2_4_2(), 2u32, _nonce_2_4_2(), _pt_2_4_2())
expect(_bytes_eq(ct_good, ct_bad)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/chacha20_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ChaCha20 RFC 7539 §2.1.1 — quarter-round test vector, ChaCha20 RFC 7539 §2.3.2 — block function test vector, ChaCha20 RFC 7539 §2.4.2 — stream encryption test vector, ChaCha20 — negative tests (wrong key / nonce / counter change output).
- ChaCha20 RFC 7539 §2.1.1 — quarter-round test vector
- ChaCha20 RFC 7539 §2.3.2 — block function test vector
- ChaCha20 RFC 7539 §2.4.2 — stream encryption test vector
- ChaCha20 — negative tests (wrong key / nonce / counter change output)

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

- Canonical SPipe generation for source `8b2b5036bdc3bcead05866eef7be1ceaeb7c0e3dfc225b9d24ee155cec82e7e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b2b5036bdc3bcead05866eef7be1ceaeb7c0e3dfc225b9d24ee155cec82e7e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b2b5036bdc3bcead05866eef7be1ceaeb7c0e3dfc225b9d24ee155cec82e7e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/chacha20_spec.spl
mirror: doc/06_spec/unit/lib/crypto/chacha20_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/chacha20_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/chacha20_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/chacha20_spec.spl:213:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces correct a after quarter-round' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/chacha20_spec.spl:219:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces correct b after quarter-round' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/chacha20_spec.spl:225:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces correct c after quarter-round' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

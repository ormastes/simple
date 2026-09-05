# Simd Dispatch Facade Specification

> Tests covering SIMD dispatch facades, utf8 counting facade, aes block facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Dispatch Facade Specification

## Scenarios

### SIMD dispatch facades

### utf8 counting facade

#### preserves mixed-width UTF-8 counting through the public entrypoints

- preserves mixed-width UTF-8 counting through the public entrypoints
   - Expected: utf8_count_codepoints(bytes) equals `3`
   - Expected: text_codepoint_len("A€😀") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves mixed-width UTF-8 counting through the public entrypoints")
val bytes = [0x41, 0xE2, 0x82, 0xAC, 0xF0, 0x9F, 0x98, 0x80]
expect(utf8_count_codepoints(bytes)).to_equal(3)
expect(text_codepoint_len("A€😀")).to_equal(3)
```

</details>

### aes block facade

#### preserves the AES-128 encrypt/decrypt known answer through the public API

- preserves the AES-128 encrypt/decrypt known answer through the public API
   - Expected: bytes_to_hex(ciphertext) equals `69c4e0d86a7b0430d8cdb78070b4c55a`
   - Expected: aes_decrypt_block(ciphertext, key) equals `plaintext`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves the AES-128 encrypt/decrypt known answer through the public API")
val key = hex_to_bytes("000102030405060708090a0b0c0d0e0f")
val plaintext = hex_to_bytes("00112233445566778899aabbccddeeff")
val ciphertext = aes_encrypt_block(plaintext, key)
expect(bytes_to_hex(ciphertext)).to_equal("69c4e0d86a7b0430d8cdb78070b4c55a")
expect(aes_decrypt_block(ciphertext, key)).to_equal(plaintext)
```

</details>

#### keeps the expanded-key block helpers wired through the same facade

- keeps the expanded-key block helpers wired through the same facade
   - Expected: bytes_to_hex(ciphertext) equals `69c4e0d86a7b0430d8cdb78070b4c55a`
   - Expected: aes_decrypt_block_with_expanded(ciphertext, expanded, 10) equals `plaintext`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the expanded-key block helpers wired through the same facade")
val key = hex_to_bytes("000102030405060708090a0b0c0d0e0f")
val plaintext = hex_to_bytes("00112233445566778899aabbccddeeff")
val expanded = expand_key(key, 16)
val ciphertext = aes_encrypt_block_with_expanded(plaintext, expanded, 10)
expect(bytes_to_hex(ciphertext)).to_equal("69c4e0d86a7b0430d8cdb78070b4c55a")
expect(aes_decrypt_block_with_expanded(ciphertext, expanded, 10)).to_equal(plaintext)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/simd_dispatch_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SIMD dispatch facades, utf8 counting facade, aes block facade.
- SIMD dispatch facades
- utf8 counting facade
- aes block facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0b0aa5a6ac516e241f27b7f072b05443dbbadedfb931cfb1d1860a9d38c23a37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b0aa5a6ac516e241f27b7f072b05443dbbadedfb931cfb1d1860a9d38c23a37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b0aa5a6ac516e241f27b7f072b05443dbbadedfb931cfb1d1860a9d38c23a37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/simd_dispatch_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/common/simd_dispatch_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/simd_dispatch_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/simd_dispatch_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/simd_dispatch_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/simd_dispatch_facade_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves mixed-width UTF-8 counting through the public entrypoints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/simd_dispatch_facade_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the AES-128 encrypt/decrypt known answer through the public API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/simd_dispatch_facade_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the expanded-key block helpers wired through the same facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

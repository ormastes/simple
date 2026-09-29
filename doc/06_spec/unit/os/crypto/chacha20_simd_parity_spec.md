# Chacha20 Simd Parity Specification

> Tests covering ChaCha20 SIMD vs scalar parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Simd Parity Specification

## Scenarios

### ChaCha20 SIMD vs scalar parity

#### RFC 8439 §2.4.2 SIMD path matches scalar on the 114-byte sunscreen vector

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- RFC 8439 §2.4.2 SIMD path matches scalar on the 114-byte sunscreen vector
   - Expected: _bytes_eq(ct_scalar, ct_simd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RFC 8439 §2.4.2 SIMD path matches scalar on the 114-byte sunscreen vector")
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct_scalar = chacha20_encrypt(key, 1u32, nonce, pt)
val ct_simd = chacha20_encrypt_simd(key, 1u32, nonce, pt)
expect(_bytes_eq(ct_scalar, ct_simd)).to_equal(true)
```

</details>

#### RFC 8439 §2.4.2 SIMD ciphertext matches the published canonical bytes

- RFC 8439 §2.4.2 SIMD ciphertext matches the published canonical bytes
   - Expected: ct.len() equals `114u64`
   - Expected: ct[0] equals `0x6eu8`
   - Expected: ct[1] equals `0x2eu8`
   - Expected: ct[2] equals `0x35u8`
   - Expected: ct[3] equals `0x9au8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RFC 8439 §2.4.2 SIMD ciphertext matches the published canonical bytes")
# Spot-check the first 4 bytes of ciphertext as published in RFC 8439:
# 0x6e, 0x2e, 0x35, 0x9a (matches the existing scalar KAT in
# test/system/os_crypto_ref_primitives_spec.spl). The SIMD path is a
# tail-only path here (114 < 256), so this verifies the scalar branch
# used inside chacha20_encrypt_simd is byte-exact too.
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct = chacha20_encrypt_simd(key, 1u32, nonce, pt)
expect(ct.len()).to_equal(114u64)
expect(ct[0]).to_equal(0x6eu8)
expect(ct[1]).to_equal(0x2eu8)
expect(ct[2]).to_equal(0x35u8)
expect(ct[3]).to_equal(0x9au8)
```

</details>

#### 256-byte aligned payload (one full SIMD chunk, no tail) matches scalar

- 256-byte aligned payload (one full SIMD chunk, no tail) matches scalar
   - Expected: ct_simd.len() equals `256u64`
   - Expected: _bytes_eq(ct_scalar, ct_simd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("256-byte aligned payload (one full SIMD chunk, no tail) matches scalar")
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _aligned256_pt()
val ct_scalar = chacha20_encrypt(key, 1u32, nonce, pt)
val ct_simd = chacha20_encrypt_simd(key, 1u32, nonce, pt)
expect(ct_simd.len()).to_equal(256u64)
expect(_bytes_eq(ct_scalar, ct_simd)).to_equal(true)
```

</details>

#### 600-byte unaligned payload (2 SIMD chunks + 88-byte tail) matches scalar

- 600-byte unaligned payload (2 SIMD chunks + 88-byte tail) matches scalar
   - Expected: ct_simd.len() equals `600u64`
   - Expected: _bytes_eq(ct_scalar, ct_simd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("600-byte unaligned payload (2 SIMD chunks + 88-byte tail) matches scalar")
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _long_pt()
val ct_scalar = chacha20_encrypt(key, 0u32, nonce, pt)
val ct_simd = chacha20_encrypt_simd(key, 0u32, nonce, pt)
expect(ct_simd.len()).to_equal(600u64)
expect(_bytes_eq(ct_scalar, ct_simd)).to_equal(true)
```

</details>

#### 1024-byte payload (4 SIMD chunks, no tail) matches scalar with non-zero counter

- 1024-byte payload (4 SIMD chunks, no tail) matches scalar with non-zero counter
   - Expected: ct_simd.len() equals `1024u64`
   - Expected: _bytes_eq(ct_scalar, ct_simd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1024-byte payload (4 SIMD chunks, no tail) matches scalar with non-zero counter")
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _kib_pt()
val ct_scalar = chacha20_encrypt(key, 7u32, nonce, pt)
val ct_simd = chacha20_encrypt_simd(key, 7u32, nonce, pt)
expect(ct_simd.len()).to_equal(1024u64)
expect(_bytes_eq(ct_scalar, ct_simd)).to_equal(true)
```

</details>

#### SIMD round-trip recovers original plaintext

- SIMD round-trip recovers original plaintext
   - Expected: _bytes_eq(recovered, pt) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIMD round-trip recovers original plaintext")
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _long_pt()
val ct = chacha20_encrypt_simd(key, 1u32, nonce, pt)
val recovered = chacha20_encrypt_simd(key, 1u32, nonce, ct)
expect(_bytes_eq(recovered, pt)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/chacha20_simd_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ChaCha20 SIMD vs scalar parity.
- ChaCha20 SIMD vs scalar parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `02c07e78b58a42672856359029e048979713528265a1a73c8bed6c4e0b4bcf2a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02c07e78b58a42672856359029e048979713528265a1a73c8bed6c4e0b4bcf2a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02c07e78b58a42672856359029e048979713528265a1a73c8bed6c4e0b4bcf2a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/chacha20_simd_parity_spec.spl
mirror: doc/06_spec/unit/os/crypto/chacha20_simd_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/chacha20_simd_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/chacha20_simd_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/chacha20_simd_parity_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RFC 8439 §2.4.2 SIMD path matches scalar on the 114-byte sunscreen vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/chacha20_simd_parity_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RFC 8439 §2.4.2 SIMD ciphertext matches the published canonical bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/chacha20_simd_parity_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '256-byte aligned payload (one full SIMD chunk, no tail) matches scalar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

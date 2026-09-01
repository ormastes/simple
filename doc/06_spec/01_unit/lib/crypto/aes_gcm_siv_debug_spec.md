# Aes Gcm Siv Debug Specification

> Tests covering AES-GCM-SIV debug: AES block encrypt sanity, AES-GCM-SIV debug: TC1 key derivation, AES-GCM-SIV debug: TC1 tag computation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Gcm Siv Debug Specification

## Scenarios

### AES-GCM-SIV debug: AES block encrypt sanity

#### FIPS 197 A.1: AES-128(zeros, zeros) = 66e94bd4ef8a2c3b884cfa59ca342b2e

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FIPS 197 A.1: AES-128(zeros, zeros) = 66e94bd4ef8a2c3b884cfa59ca342b2e
   - Expected: _equal_bytes(result, _fips197_expected()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIPS 197 A.1: AES-128(zeros, zeros) = 66e94bd4ef8a2c3b884cfa59ca342b2e")
val result = _aes128_enc(_fips197_key(), _fips197_block())
expect(_equal_bytes(result, _fips197_expected())).to_equal(true)
```

</details>

### AES-GCM-SIV debug: TC1 key derivation

#### KD enc0 = AES_kgk(LE32(0)||nonce) has correct first 8 bytes (auth_key[:8] = d9b36027 96949 41a)

- KD enc0 = AES_kgk(LE32(0)||nonce) has correct first 8 bytes (auth_key[:8] = d9b36027 96949 41a)
   - Expected: _equal_bytes(got8, expected_first8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KD enc0 = AES_kgk(LE32(0)||nonce) has correct first 8 bytes (auth_key[:8] = d9b36027 96949 41a)")
val enc0 = _aes128_enc(_tc1_kgk(), _tc1_kd_block0())
# auth_key[:8] should be d9 b3 60 27 96 94 94 1a
val expected_first8: [u8] = [0xd9u8, 0xb3u8, 0x60u8, 0x27u8, 0x96u8, 0x94u8, 0x94u8, 0x1au8]
var got8: [u8] = []
var i: u64 = 0
while i < 8:
    got8.push(enc0.get(i))
    i = i + 1
expect(_equal_bytes(got8, expected_first8)).to_equal(true)
```

</details>

#### KD enc1 = AES_kgk(LE32(1)||nonce) has correct first 8 bytes (auth_key[8:16] = c5dbc698 7ada7377)

- KD enc1 = AES_kgk(LE32(1)||nonce) has correct first 8 bytes (auth_key[8:16] = c5dbc698 7ada7377)
   - Expected: _equal_bytes(got8, expected_second8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KD enc1 = AES_kgk(LE32(1)||nonce) has correct first 8 bytes (auth_key[8:16] = c5dbc698 7ada7377)")
val enc1 = _aes128_enc(_tc1_kgk(), _tc1_kd_block1())
val expected_second8: [u8] = [0xc5u8, 0xdbu8, 0xc6u8, 0x98u8, 0x7au8, 0xdau8, 0x73u8, 0x77u8]
var got8: [u8] = []
var i: u64 = 0
while i < 8:
    got8.push(enc1.get(i))
    i = i + 1
expect(_equal_bytes(got8, expected_second8)).to_equal(true)
```

</details>

#### KD enc2 = AES_kgk(LE32(2)||nonce) has correct first 8 bytes (enc_key[:8] = 4004a0dc d862f2a5)

- KD enc2 = AES_kgk(LE32(2)||nonce) has correct first 8 bytes (enc_key[:8] = 4004a0dc d862f2a5)
   - Expected: _equal_bytes(got8, expected_8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KD enc2 = AES_kgk(LE32(2)||nonce) has correct first 8 bytes (enc_key[:8] = 4004a0dc d862f2a5)")
val enc2 = _aes128_enc(_tc1_kgk(), _tc1_kd_block2())
val expected_8: [u8] = [0x40u8, 0x04u8, 0xa0u8, 0xdcu8, 0xd8u8, 0x62u8, 0xf2u8, 0xa5u8]
var got8: [u8] = []
var i: u64 = 0
while i < 8:
    got8.push(enc2.get(i))
    i = i + 1
expect(_equal_bytes(got8, expected_8)).to_equal(true)
```

</details>

#### KD enc3 = AES_kgk(LE32(3)||nonce) has correct first 8 bytes (enc_key[8:16] = 7360219d 2d44ef6c)

- KD enc3 = AES_kgk(LE32(3)||nonce) has correct first 8 bytes (enc_key[8:16] = 7360219d 2d44ef6c)
   - Expected: _equal_bytes(got8, expected_8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KD enc3 = AES_kgk(LE32(3)||nonce) has correct first 8 bytes (enc_key[8:16] = 7360219d 2d44ef6c)")
val enc3 = _aes128_enc(_tc1_kgk(), _tc1_kd_block3())
val expected_8: [u8] = [0x73u8, 0x60u8, 0x21u8, 0x9du8, 0x2du8, 0x44u8, 0xefu8, 0x6cu8]
var got8: [u8] = []
var i: u64 = 0
while i < 8:
    got8.push(enc3.get(i))
    i = i + 1
expect(_equal_bytes(got8, expected_8)).to_equal(true)
```

</details>

### AES-GCM-SIV debug: TC1 tag computation

#### TC1 full encrypt = dc20e2d8... (empty PT, empty AAD)

- TC1 full encrypt = dc20e2d8... (empty PT, empty AAD)
   - Expected: _equal_bytes(computed_tag, _tc1_expected_tag()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1 full encrypt = dc20e2d8... (empty PT, empty AAD)")
# With correct auth/enc keys, POLYVAL(zeros) = 0, XOR nonce[0:12], mask bit127, AES_enc_key
# AES_enc_key(0 XOR 03000000000000000000000000000000 & ~bit127)
# = AES_enc_key(030000000000000000000000 || 00...00 with bit127 cleared)
# = tag dc20e2d83f25705bb49e439eca56de25
val enc_key = _expected_enc_key()
# Build s = nonce_xor_masked = nonce padded to 16 bytes, bit127 cleared
# nonce = 030000000000000000000000 -> pad with 0x00, 0x00, 0x00, 0x00 (4 zero bytes at end)
# XOR with POLYVAL result (all zeros) = no change
# bit127 clear: byte15 & 0x7F = 0x00 (already clear)
val s_masked: [u8] = [0x03u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
                       0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
val computed_tag = _aes128_enc(enc_key, s_masked)
expect(_equal_bytes(computed_tag, _tc1_expected_tag())).to_equal(true)
```

</details>

#### TC1 aes128_gcm_siv_encrypt gives correct tag

- TC1 aes128_gcm_siv_encrypt gives correct tag
   - Expected: _equal_bytes(result, _tc1_expected_tag()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1 aes128_gcm_siv_encrypt gives correct tag")
val key: [u8] = [0x01u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
                  0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
val nonce: [u8] = [0x03u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
                    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
val result = aes128_gcm_siv_encrypt(key, nonce, [], [])
expect(_equal_bytes(result, _tc1_expected_tag())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes_gcm_siv_debug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES-GCM-SIV debug: AES block encrypt sanity, AES-GCM-SIV debug: TC1 key derivation, AES-GCM-SIV debug: TC1 tag computation.
- AES-GCM-SIV debug: AES block encrypt sanity
- AES-GCM-SIV debug: TC1 key derivation
- AES-GCM-SIV debug: TC1 tag computation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `262e8711bc5a013bda2a9ee10402b67339c7c700ca5fb25b3acbd590cbcc7957`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `262e8711bc5a013bda2a9ee10402b67339c7c700ca5fb25b3acbd590cbcc7957`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `262e8711bc5a013bda2a9ee10402b67339c7c700ca5fb25b3acbd590cbcc7957`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/aes_gcm_siv_debug_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/aes_gcm_siv_debug_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/aes_gcm_siv_debug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/aes_gcm_siv_debug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/aes_gcm_siv_debug_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FIPS 197 A.1: AES-128(zeros, zeros) = 66e94bd4ef8a2c3b884cfa59ca342b2e' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/aes_gcm_siv_debug_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'KD enc0 = AES_kgk(LE32(0)||nonce) has correct first 8 bytes (auth_key[:8] = d9b36027 96949 41a)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/aes_gcm_siv_debug_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'KD enc1 = AES_kgk(LE32(1)||nonce) has correct first 8 bytes (auth_key[8:16] = c5dbc698 7ada7377)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

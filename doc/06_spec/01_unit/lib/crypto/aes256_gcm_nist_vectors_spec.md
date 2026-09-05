# Aes256 Gcm Nist Vectors Specification

> Tests covering AES-256-GCM NIST SP 800-38D Appendix B vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes256 Gcm Nist Vectors Specification

## Scenarios

### AES-256-GCM NIST SP 800-38D Appendix B vectors

#### TC13 encrypt: empty PT + empty AAD - tag matches NIST SP 800-38D B.13

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TC13 encrypt: empty PT + empty AAD - tag matches NIST SP 800-38D B.13
   - Expected: ct.len() equals `0`
   - Expected: tag equals `_tc13_expected_tag()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC13 encrypt: empty PT + empty AAD - tag matches NIST SP 800-38D B.13")
val empty: [u8] = []
val out = aes256_gcm_encrypt(_tc13_key(), _tc13_nonce(), empty, empty)
val ct = _split_ct(out, 0)
val tag = _split_tag(out, 0)
expect(ct.len()).to_equal(0)
expect(tag).to_equal(_tc13_expected_tag())
```

</details>

#### TC13 decrypt: correct tag succeeds with empty plaintext

- TC13 decrypt: correct tag succeeds with empty plaintext
   - Expected: data.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC13 decrypt: correct tag succeeds with empty plaintext")
val empty: [u8] = []
val result = aes256_gcm_decrypt(_tc13_key(), _tc13_nonce(), empty, empty, _tc13_expected_tag())
match result:
    Aes256GcmResult.Ok(data):
        expect(data.len()).to_equal(0)
    Aes256GcmResult.Err(msg):
        fail("unexpected AES-256-GCM vector result branch")
```

</details>

#### TC13 decrypt: corrupted tag is rejected

- TC13 decrypt: corrupted tag is rejected
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC13 decrypt: corrupted tag is rejected")
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc13_expected_tag())
val result = aes256_gcm_decrypt(_tc13_key(), _tc13_nonce(), empty, empty, bad_tag)
match result:
    Aes256GcmResult.Ok(data):
        fail("unexpected AES-256-GCM vector result branch")
    Aes256GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC14 encrypt: 16-byte zero PT, empty AAD - ciphertext and tag match NIST SP 800-38D B.14

- TC14 encrypt: 16-byte zero PT, empty AAD - ciphertext and tag match NIST SP 800-38D B.14
   - Expected: ct equals `_tc14_expected_ct()`
   - Expected: tag equals `_tc14_expected_tag()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC14 encrypt: 16-byte zero PT, empty AAD - ciphertext and tag match NIST SP 800-38D B.14")
val empty: [u8] = []
val out = aes256_gcm_encrypt(_tc14_key(), _tc14_nonce(), _tc14_plaintext(), empty)
val ct = _split_ct(out, 16)
val tag = _split_tag(out, 16)
expect(ct).to_equal(_tc14_expected_ct())
expect(tag).to_equal(_tc14_expected_tag())
```

</details>

#### TC14 decrypt: correct tag returns original plaintext

- TC14 decrypt: correct tag returns original plaintext
   - Expected: data equals `_tc14_plaintext()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC14 decrypt: correct tag returns original plaintext")
val empty: [u8] = []
val result = aes256_gcm_decrypt(_tc14_key(), _tc14_nonce(), _tc14_expected_ct(), empty, _tc14_expected_tag())
match result:
    Aes256GcmResult.Ok(data):
        expect(data).to_equal(_tc14_plaintext())
    Aes256GcmResult.Err(msg):
        fail("unexpected AES-256-GCM vector result branch")
```

</details>

#### TC14 decrypt: corrupted tag is rejected

- TC14 decrypt: corrupted tag is rejected
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC14 decrypt: corrupted tag is rejected")
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc14_expected_tag())
val result = aes256_gcm_decrypt(_tc14_key(), _tc14_nonce(), _tc14_expected_ct(), empty, bad_tag)
match result:
    Aes256GcmResult.Ok(data):
        fail("unexpected AES-256-GCM vector result branch")
    Aes256GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC15 encrypt: 64-byte PT, empty AAD - ciphertext and tag match NIST SP 800-38D B.15

- TC15 encrypt: 64-byte PT, empty AAD - ciphertext and tag match NIST SP 800-38D B.15
   - Expected: ct equals `_tc15_expected_ct()`
   - Expected: tag equals `_tc15_expected_tag()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC15 encrypt: 64-byte PT, empty AAD - ciphertext and tag match NIST SP 800-38D B.15")
val empty: [u8] = []
val out = aes256_gcm_encrypt(_tc15_key(), _tc15_nonce(), _tc15_plaintext(), empty)
val ct = _split_ct(out, 64)
val tag = _split_tag(out, 64)
expect(ct).to_equal(_tc15_expected_ct())
expect(tag).to_equal(_tc15_expected_tag())
```

</details>

#### TC15 decrypt: correct tag returns original plaintext

- TC15 decrypt: correct tag returns original plaintext
   - Expected: data equals `_tc15_plaintext()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC15 decrypt: correct tag returns original plaintext")
val empty: [u8] = []
val result = aes256_gcm_decrypt(_tc15_key(), _tc15_nonce(), _tc15_expected_ct(), empty, _tc15_expected_tag())
match result:
    Aes256GcmResult.Ok(data):
        expect(data).to_equal(_tc15_plaintext())
    Aes256GcmResult.Err(msg):
        fail("unexpected AES-256-GCM vector result branch")
```

</details>

#### TC15 decrypt: corrupted tag is rejected

- TC15 decrypt: corrupted tag is rejected
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC15 decrypt: corrupted tag is rejected")
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc15_expected_tag())
val result = aes256_gcm_decrypt(_tc15_key(), _tc15_nonce(), _tc15_expected_ct(), empty, bad_tag)
match result:
    Aes256GcmResult.Ok(data):
        fail("unexpected AES-256-GCM vector result branch")
    Aes256GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC16 encrypt: 60-byte PT, 20-byte AAD - ciphertext and tag match NIST SP 800-38D B.16

- TC16 encrypt: 60-byte PT, 20-byte AAD - ciphertext and tag match NIST SP 800-38D B.16
   - Expected: ct equals `_tc16_expected_ct()`
   - Expected: tag equals `_tc16_expected_tag()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC16 encrypt: 60-byte PT, 20-byte AAD - ciphertext and tag match NIST SP 800-38D B.16")
val out = aes256_gcm_encrypt(_tc16_key(), _tc16_nonce(), _tc16_plaintext(), _tc16_aad())
val ct = _split_ct(out, 60)
val tag = _split_tag(out, 60)
expect(ct).to_equal(_tc16_expected_ct())
expect(tag).to_equal(_tc16_expected_tag())
```

</details>

#### TC16 decrypt: correct tag returns original plaintext

- TC16 decrypt: correct tag returns original plaintext
   - Expected: data equals `_tc16_plaintext()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC16 decrypt: correct tag returns original plaintext")
val result = aes256_gcm_decrypt(_tc16_key(), _tc16_nonce(), _tc16_expected_ct(), _tc16_aad(), _tc16_expected_tag())
match result:
    Aes256GcmResult.Ok(data):
        expect(data).to_equal(_tc16_plaintext())
    Aes256GcmResult.Err(msg):
        fail("unexpected AES-256-GCM vector result branch")
```

</details>

#### TC16 decrypt: corrupted tag is rejected

- TC16 decrypt: corrupted tag is rejected
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TC16 decrypt: corrupted tag is rejected")
val bad_tag = _corrupt_last_byte(_tc16_expected_tag())
val result = aes256_gcm_decrypt(_tc16_key(), _tc16_nonce(), _tc16_expected_ct(), _tc16_aad(), bad_tag)
match result:
    Aes256GcmResult.Ok(data):
        fail("unexpected AES-256-GCM vector result branch")
    Aes256GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES-256-GCM NIST SP 800-38D Appendix B vectors.
- AES-256-GCM NIST SP 800-38D Appendix B vectors

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e8fbfcbc12cbc0238971fa4cfe1e979d09e9a675b1ff3dc82b6a293b9cd0958a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e8fbfcbc12cbc0238971fa4cfe1e979d09e9a675b1ff3dc82b6a293b9cd0958a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e8fbfcbc12cbc0238971fa4cfe1e979d09e9a675b1ff3dc82b6a293b9cd0958a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.spl:202:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC13 encrypt: empty PT + empty AAD - tag matches NIST SP 800-38D B.13' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.spl:212:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC13 decrypt: correct tag succeeds with empty plaintext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.spl:223:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC13 decrypt: corrupted tag is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

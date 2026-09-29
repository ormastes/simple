# Aes128 Gcm Nist Vectors Specification

> Tests covering AES-128-GCM NIST SP 800-38D Appendix B vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes128 Gcm Nist Vectors Specification

## Scenarios

### AES-128-GCM NIST SP 800-38D Appendix B vectors

#### TC1 encrypt: empty PT + empty AAD — tag matches NIST SP 800-38D B.1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TC1 encrypt: empty PT + empty AAD — tag matches NIST SP 800-38D B.1
   - Expected: ct.len() equals `0`
   - Expected: tag equals `_tc1_expected_tag()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1 encrypt: empty PT + empty AAD — tag matches NIST SP 800-38D B.1")
val empty: [u8] = []
val out = aes128_gcm_encrypt(_tc1_key(), _tc1_nonce(), empty, empty)
val ct = _split_ct(out, 0)
val tag = _split_tag(out, 0)
expect(ct.len()).to_equal(0)
expect(tag).to_equal(_tc1_expected_tag())
```

</details>

#### TC1 decrypt: correct tag succeeds with empty plaintext

- TC1 decrypt: correct tag succeeds with empty plaintext
   - Expected: data.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1 decrypt: correct tag succeeds with empty plaintext")
val empty: [u8] = []
val result = aes128_gcm_decrypt(_tc1_key(), _tc1_nonce(), empty, empty, _tc1_expected_tag())
match result:
    Aes128GcmResult.Ok(data):
        expect(data.len()).to_equal(0)
    Aes128GcmResult.Err(msg):
        fail("unexpected AES-128-GCM vector result branch")
```

</details>

#### TC1 decrypt: corrupted tag is rejected

- TC1 decrypt: corrupted tag is rejected
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1 decrypt: corrupted tag is rejected")
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc1_expected_tag())
val result = aes128_gcm_decrypt(_tc1_key(), _tc1_nonce(), empty, empty, bad_tag)
match result:
    Aes128GcmResult.Ok(data):
        fail("unexpected AES-128-GCM vector result branch")
    Aes128GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC2 encrypt: 16-byte zero PT, empty AAD — ciphertext and tag match NIST SP 800-38D B.2

- TC2 encrypt: 16-byte zero PT, empty AAD — ciphertext and tag match NIST SP 800-38D B.2
   - Expected: ct equals `_tc2_expected_ct()`
   - Expected: tag equals `_tc2_expected_tag()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2 encrypt: 16-byte zero PT, empty AAD — ciphertext and tag match NIST SP 800-38D B.2")
val empty: [u8] = []
val out = aes128_gcm_encrypt(_tc2_key(), _tc2_nonce(), _tc2_plaintext(), empty)
val ct = _split_ct(out, 16)
val tag = _split_tag(out, 16)
expect(ct).to_equal(_tc2_expected_ct())
expect(tag).to_equal(_tc2_expected_tag())
```

</details>

#### TC2 decrypt: correct tag returns original plaintext

- TC2 decrypt: correct tag returns original plaintext
   - Expected: data equals `_tc2_plaintext()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2 decrypt: correct tag returns original plaintext")
val empty: [u8] = []
val result = aes128_gcm_decrypt(_tc2_key(), _tc2_nonce(), _tc2_expected_ct(), empty, _tc2_expected_tag())
match result:
    Aes128GcmResult.Ok(data):
        expect(data).to_equal(_tc2_plaintext())
    Aes128GcmResult.Err(msg):
        fail("unexpected AES-128-GCM vector result branch")
```

</details>

#### TC2 decrypt: corrupted tag is rejected

- TC2 decrypt: corrupted tag is rejected
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2 decrypt: corrupted tag is rejected")
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc2_expected_tag())
val result = aes128_gcm_decrypt(_tc2_key(), _tc2_nonce(), _tc2_expected_ct(), empty, bad_tag)
match result:
    Aes128GcmResult.Ok(data):
        fail("unexpected AES-128-GCM vector result branch")
    Aes128GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC3 encrypt: 64-byte PT, empty AAD — ciphertext and tag match NIST SP 800-38D B.3

- TC3 encrypt: 64-byte PT, empty AAD — ciphertext and tag match NIST SP 800-38D B.3
   - Expected: ct equals `_tc3_expected_ct()`
   - Expected: tag equals `_tc3_expected_tag()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC3 encrypt: 64-byte PT, empty AAD — ciphertext and tag match NIST SP 800-38D B.3")
val empty: [u8] = []
val out = aes128_gcm_encrypt(_tc3_key(), _tc3_nonce(), _tc3_plaintext(), empty)
val ct = _split_ct(out, 64)
val tag = _split_tag(out, 64)
expect(ct).to_equal(_tc3_expected_ct())
expect(tag).to_equal(_tc3_expected_tag())
```

</details>

#### TC3 decrypt: correct tag returns original plaintext

- TC3 decrypt: correct tag returns original plaintext
   - Expected: data equals `_tc3_plaintext()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC3 decrypt: correct tag returns original plaintext")
val empty: [u8] = []
val result = aes128_gcm_decrypt(_tc3_key(), _tc3_nonce(), _tc3_expected_ct(), empty, _tc3_expected_tag())
match result:
    Aes128GcmResult.Ok(data):
        expect(data).to_equal(_tc3_plaintext())
    Aes128GcmResult.Err(msg):
        fail("unexpected AES-128-GCM vector result branch")
```

</details>

#### TC3 decrypt: corrupted tag is rejected

- TC3 decrypt: corrupted tag is rejected
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC3 decrypt: corrupted tag is rejected")
val empty: [u8] = []
val bad_tag = _corrupt_last_byte(_tc3_expected_tag())
val result = aes128_gcm_decrypt(_tc3_key(), _tc3_nonce(), _tc3_expected_ct(), empty, bad_tag)
match result:
    Aes128GcmResult.Ok(data):
        fail("unexpected AES-128-GCM vector result branch")
    Aes128GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

#### TC4 encrypt: 60-byte PT, 20-byte AAD — ciphertext and tag match NIST SP 800-38D B.4

- TC4 encrypt: 60-byte PT, 20-byte AAD — ciphertext and tag match NIST SP 800-38D B.4
   - Expected: ct equals `_tc4_expected_ct()`
   - Expected: tag equals `_tc4_expected_tag()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC4 encrypt: 60-byte PT, 20-byte AAD — ciphertext and tag match NIST SP 800-38D B.4")
val out = aes128_gcm_encrypt(_tc4_key(), _tc4_nonce(), _tc4_plaintext(), _tc4_aad())
val ct = _split_ct(out, 60)
val tag = _split_tag(out, 60)
expect(ct).to_equal(_tc4_expected_ct())
expect(tag).to_equal(_tc4_expected_tag())
```

</details>

#### TC4 decrypt: correct tag returns original plaintext

- TC4 decrypt: correct tag returns original plaintext
   - Expected: data equals `_tc4_plaintext()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC4 decrypt: correct tag returns original plaintext")
val result = aes128_gcm_decrypt(_tc4_key(), _tc4_nonce(), _tc4_expected_ct(), _tc4_aad(), _tc4_expected_tag())
match result:
    Aes128GcmResult.Ok(data):
        expect(data).to_equal(_tc4_plaintext())
    Aes128GcmResult.Err(msg):
        fail("unexpected AES-128-GCM vector result branch")
```

</details>

#### TC4 decrypt: corrupted tag is rejected

- TC4 decrypt: corrupted tag is rejected
   - Expected: msg equals `authentication tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC4 decrypt: corrupted tag is rejected")
val bad_tag = _corrupt_last_byte(_tc4_expected_tag())
val result = aes128_gcm_decrypt(_tc4_key(), _tc4_nonce(), _tc4_expected_ct(), _tc4_aad(), bad_tag)
match result:
    Aes128GcmResult.Ok(data):
        fail("unexpected AES-128-GCM vector result branch")
    Aes128GcmResult.Err(msg):
        expect(msg).to_equal("authentication tag mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES-128-GCM NIST SP 800-38D Appendix B vectors.
- AES-128-GCM NIST SP 800-38D Appendix B vectors

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

- Canonical SPipe generation for source `997b7c94659cd518984f90e591242228e5ccdf6923c3e3d47e87f44dc96f332d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `997b7c94659cd518984f90e591242228e5ccdf6923c3e3d47e87f44dc96f332d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `997b7c94659cd518984f90e591242228e5ccdf6923c3e3d47e87f44dc96f332d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl
mirror: doc/06_spec/unit/lib/crypto/aes128_gcm_nist_vectors_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/aes128_gcm_nist_vectors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/aes128_gcm_nist_vectors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl:209:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC1 encrypt: empty PT + empty AAD — tag matches NIST SP 800-38D B.1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl:219:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC1 decrypt: correct tag succeeds with empty plaintext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl:230:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC1 decrypt: corrupted tag is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

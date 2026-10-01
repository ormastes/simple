# Aes Ctr Nist Specification

> Tests covering AES-CTR NIST SP 800-38A Appendix F.5 vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Ctr Nist Specification

## Scenarios

### AES-CTR NIST SP 800-38A Appendix F.5 vectors

#### F.5.1 AES-128-CTR encrypts 4-block plaintext correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- F.5.1 AES-128-CTR encrypts 4-block plaintext correctly
   - Expected: ct equals `_expected_ct_aes128()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.5.1 AES-128-CTR encrypts 4-block plaintext correctly")
val ct = aes_ctr_encrypt(_plaintext_f5(), _key_aes128(), _iv_f5())
expect(ct).to_equal(_expected_ct_aes128())
```

</details>

#### F.5.2 AES-128-CTR decrypts back to plaintext

- F.5.2 AES-128-CTR decrypts back to plaintext
   - Expected: pt equals `_plaintext_f5()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.5.2 AES-128-CTR decrypts back to plaintext")
val pt = aes_ctr_decrypt(_expected_ct_aes128(), _key_aes128(), _iv_f5())
expect(pt).to_equal(_plaintext_f5())
```

</details>

#### F.5.5 AES-256-CTR encrypts 4-block plaintext correctly

- F.5.5 AES-256-CTR encrypts 4-block plaintext correctly
   - Expected: ct equals `_expected_ct_aes256()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.5.5 AES-256-CTR encrypts 4-block plaintext correctly")
val ct = aes_ctr_encrypt(_plaintext_f5(), _key_aes256(), _iv_f5())
expect(ct).to_equal(_expected_ct_aes256())
```

</details>

#### F.5.6 AES-256-CTR decrypts back to plaintext

- F.5.6 AES-256-CTR decrypts back to plaintext
   - Expected: pt equals `_plaintext_f5()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.5.6 AES-256-CTR decrypts back to plaintext")
val pt = aes_ctr_decrypt(_expected_ct_aes256(), _key_aes256(), _iv_f5())
expect(pt).to_equal(_plaintext_f5())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/aes_ctr_nist_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES-CTR NIST SP 800-38A Appendix F.5 vectors.
- AES-CTR NIST SP 800-38A Appendix F.5 vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `5c50d9da8105c2f686e0fde359e1f6570cee7ee0b5e9d9282bbef4fd411333c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c50d9da8105c2f686e0fde359e1f6570cee7ee0b5e9d9282bbef4fd411333c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c50d9da8105c2f686e0fde359e1f6570cee7ee0b5e9d9282bbef4fd411333c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/aes_ctr_nist_spec.spl
mirror: doc/06_spec/unit/lib/crypto/aes_ctr_nist_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/aes_ctr_nist_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/aes_ctr_nist_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/aes_ctr_nist_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F.5.1 AES-128-CTR encrypts 4-block plaintext correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/aes_ctr_nist_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F.5.2 AES-128-CTR decrypts back to plaintext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/aes_ctr_nist_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F.5.5 AES-256-CTR encrypts 4-block plaintext correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Authenticated Decryption Rejects Tampering Specification

> Tests covering authenticated decryption must reject any tampered ciphertext.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Authenticated Decryption Rejects Tampering Specification

## Scenarios

### authenticated decryption must reject any tampered ciphertext

#### each tampered variant really differs from the original token

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- each tampered variant really differs from the original token
   - Expected: _really_tampered_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each tampered variant really differs from the original token")
expect(_really_tampered_count()).to_equal(3)
```

</details>

#### no tampered variant is accepted, in the nonce, ciphertext or MAC region

- no tampered variant is accepted, in the nonce, ciphertext or MAC region
   - Expected: _accepted_tamper_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no tampered variant is accepted, in the nonce, ciphertext or MAC region")
expect(_accepted_tamper_count()).to_equal(0)
```

</details>

#### the untampered token still decrypts, so rejection is not blanket

- the untampered token still decrypts, so rejection is not blanket
   - Expected: _decrypt_ok(_token_text()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the untampered token still decrypts, so rejection is not blanket")
expect(_decrypt_ok(_token_text())).to_equal(true)
```

</details>

#### the untampered token decrypts to the exact original plaintext

- the untampered token decrypts to the exact original plaintext
   - Expected: _decrypted_text() equals `_plaintext()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the untampered token decrypts to the exact original plaintext")
expect(_decrypted_text()).to_equal(_plaintext())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/authenticated_decryption_rejects_tampering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering authenticated decryption must reject any tampered ciphertext.
- authenticated decryption must reject any tampered ciphertext

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

- Canonical SPipe generation for source `f243f30a50982f4f1e88296959de85bdd95279ad1dab31594dd027b23dde0109`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f243f30a50982f4f1e88296959de85bdd95279ad1dab31594dd027b23dde0109`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f243f30a50982f4f1e88296959de85bdd95279ad1dab31594dd027b23dde0109`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/crypto/authenticated_decryption_rejects_tampering_spec.spl
mirror: doc/06_spec/unit/lib/crypto/authenticated_decryption_rejects_tampering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/authenticated_decryption_rejects_tampering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/authenticated_decryption_rejects_tampering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/authenticated_decryption_rejects_tampering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/crypto/authenticated_decryption_rejects_tampering_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'each tampered variant really differs from the original token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/authenticated_decryption_rejects_tampering_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no tampered variant is accepted, in the nonce, ciphertext or MAC region' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/authenticated_decryption_rejects_tampering_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the untampered token still decrypts, so rejection is not blanket' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Ed448 Rfc8032 Kat Specification

> Tests covering Ed448 RFC 8032 §7.4 test vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ed448 Rfc8032 Kat Specification

## Scenarios

### Ed448 RFC 8032 §7.4 test vectors

#### T1: derived public key matches RFC 8032 §7.4 Blank vector

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- T1: derived public key matches RFC 8032 §7.4 Blank vector
   - Expected: kp.1 equals `PUB_T1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T1: derived public key matches RFC 8032 §7.4 Blank vector")
val kp = ed448_keygen(SEED_T1)
expect(kp.1).to_equal(PUB_T1)
```

</details>

#### T1: sign(empty) byte-matches RFC 8032 §7.4 expected signature

- T1: sign(empty) byte-matches RFC 8032 §7.4 expected signature
   - Expected: sig equals `SIG_T1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T1: sign(empty) byte-matches RFC 8032 §7.4 expected signature")
val kp = ed448_keygen(SEED_T1)
val sig = ed448_sign(kp.0, kp.1, [], [])
expect(sig).to_equal(SIG_T1)
```

</details>

#### T1: signature verifies under the correct public key

- T1: signature verifies under the correct public key
   - Expected: ed448_verify(PUB_T1, [], SIG_T1, []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T1: signature verifies under the correct public key")
expect(ed448_verify(PUB_T1, [], SIG_T1, [])).to_equal(true)
```

</details>

#### T1: signature is rejected when the S half is bit-flipped

- T1: signature is rejected when the S half is bit-flipped
   - Expected: ed448_verify(PUB_T1, [], bad_sig, []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T1: signature is rejected when the S half is bit-flipped")
# Flip a bit inside S (offset 57 = first byte of S half) — more
# sensitive than R-flips, which can collide with a different valid R.
val bad_sig = _flip_byte(SIG_T1, 57)
expect(ed448_verify(PUB_T1, [], bad_sig, [])).to_equal(false)
```

</details>

#### T2: derived public key matches RFC 8032 §7.4 1-octet vector

- T2: derived public key matches RFC 8032 §7.4 1-octet vector
   - Expected: kp.1 equals `PUB_T2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T2: derived public key matches RFC 8032 §7.4 1-octet vector")
val kp = ed448_keygen(SEED_T2)
expect(kp.1).to_equal(PUB_T2)
```

</details>

#### T2: sign(0x03) byte-matches RFC 8032 §7.4 expected signature

- T2: sign(0x03) byte-matches RFC 8032 §7.4 expected signature
   - Expected: sig equals `SIG_T2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T2: sign(0x03) byte-matches RFC 8032 §7.4 expected signature")
val kp = ed448_keygen(SEED_T2)
val sig = ed448_sign(kp.0, kp.1, MSG_T2, [])
expect(sig).to_equal(SIG_T2)
```

</details>

#### T2: signature verifies under the correct public key

- T2: signature verifies under the correct public key
   - Expected: ed448_verify(PUB_T2, MSG_T2, SIG_T2, []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T2: signature verifies under the correct public key")
expect(ed448_verify(PUB_T2, MSG_T2, SIG_T2, [])).to_equal(true)
```

</details>

#### T2: signature is rejected under a different public key

- T2: signature is rejected under a different public key
   - Expected: ed448_verify(PUB_T1, MSG_T2, SIG_T2, []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T2: signature is rejected under a different public key")
expect(ed448_verify(PUB_T1, MSG_T2, SIG_T2, [])).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Ed448 RFC 8032 §7.4 test vectors.
- Ed448 RFC 8032 §7.4 test vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `8f8ddabbe5b2c8871edd7e495d4b181b17cf4f90356e82af853c1dd85fdff871`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f8ddabbe5b2c8871edd7e495d4b181b17cf4f90356e82af853c1dd85fdff871`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f8ddabbe5b2c8871edd7e495d4b181b17cf4f90356e82af853c1dd85fdff871`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl
mirror: doc/06_spec/unit/lib/crypto/ed448_rfc8032_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/ed448_rfc8032_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/ed448_rfc8032_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T1: derived public key matches RFC 8032 §7.4 Blank vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T1: sign(empty) byte-matches RFC 8032 §7.4 expected signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T1: signature verifies under the correct public key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Ml Dsa 44 Kat Specification

> Tests covering ML-DSA-44 KeyGen sizes, ML-DSA-44 end-to-end Sign + Verify.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ml Dsa 44 Kat Specification

## Scenarios

### ML-DSA-44 KeyGen sizes

#### ml_dsa_keygen_44 produces pk of size 1312 bytes (FIPS 204 §B Table 2)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ml_dsa_keygen_44 produces pk of size 1312 bytes (FIPS 204 §B Table 2)
   - Expected: _keygen_pk_len() equals `1312`
   - Expected: _keygen_pk_len() equals `pk_size_44()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ml_dsa_keygen_44 produces pk of size 1312 bytes (FIPS 204 §B Table 2)")
expect(_keygen_pk_len()).to_equal(1312)
expect(_keygen_pk_len()).to_equal(pk_size_44())
```

</details>

#### ml_dsa_keygen_44 produces sk of size 2560 bytes (FIPS 204 §B Table 2)

- ml_dsa_keygen_44 produces sk of size 2560 bytes (FIPS 204 §B Table 2)
   - Expected: _keygen_sk_len() equals `2560`
   - Expected: _keygen_sk_len() equals `sk_size_44()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ml_dsa_keygen_44 produces sk of size 2560 bytes (FIPS 204 §B Table 2)")
expect(_keygen_sk_len()).to_equal(2560)
expect(_keygen_sk_len()).to_equal(sk_size_44())
```

</details>

### ML-DSA-44 end-to-end Sign + Verify

#### Sign(sk, m) → σ; Verify(pk, m, σ) == true

- Sign(sk, m) → σ; Verify(pk, m, σ) == true
   - Expected: _sign_verify_round_trip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sign(sk, m) → σ; Verify(pk, m, σ) == true")
expect(_sign_verify_round_trip()).to_equal(true)
```

</details>

#### Verify rejects bit-flipped message

- Verify rejects bit-flipped message
   - Expected: _verify_rejects_tampered_msg() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify rejects bit-flipped message")
expect(_verify_rejects_tampered_msg()).to_equal(true)
```

</details>

#### Verify rejects bit-flipped signature (c_tilde)

- Verify rejects bit-flipped signature (c_tilde)
   - Expected: _verify_rejects_tampered_sig() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify rejects bit-flipped signature (c_tilde)")
expect(_verify_rejects_tampered_sig()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/ml_dsa_44_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ML-DSA-44 KeyGen sizes, ML-DSA-44 end-to-end Sign + Verify.
- ML-DSA-44 KeyGen sizes
- ML-DSA-44 end-to-end Sign + Verify

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `b6462152506f98c310215f22e3e936fa68900993bbebc99f3d7af00c0fe6f37f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6462152506f98c310215f22e3e936fa68900993bbebc99f3d7af00c0fe6f37f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6462152506f98c310215f22e3e936fa68900993bbebc99f3d7af00c0fe6f37f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/crypto/ml_dsa_44_kat_spec.spl
mirror: doc/06_spec/unit/lib/crypto/ml_dsa_44_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/ml_dsa_44_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/ml_dsa_44_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/ml_dsa_44_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/crypto/ml_dsa_44_kat_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ml_dsa_keygen_44 produces pk of size 1312 bytes (FIPS 204 §B Table 2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/ml_dsa_44_kat_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ml_dsa_keygen_44 produces sk of size 2560 bytes (FIPS 204 §B Table 2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/ml_dsa_44_kat_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Sign(sk, m) → σ; Verify(pk, m, σ) == true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

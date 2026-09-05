# Ml Kem 512 Kat Specification

> Tests covering ML-KEM-512 size invariants (FIPS 203 §8 Table 3), ML-KEM-512 parameter table (FIPS 203 §2.3 Table 2), ML-KEM-512 deterministic round-trip (top-level harness).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ml Kem 512 Kat Specification

## Scenarios

### ML-KEM-512 size invariants (FIPS 203 §8 Table 3)

#### ITEM-1a ek = 800 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ITEM-1a ek = 800 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-1a ek = 800 bytes")
ml_kem_512_ek_bytes().to_equal(800)
```

</details>

#### ITEM-1b dk = 1632 bytes

- ITEM-1b dk = 1632 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-1b dk = 1632 bytes")
ml_kem_512_dk_bytes().to_equal(1632)
```

</details>

#### ITEM-1c ciphertext = 768 bytes

- ITEM-1c ciphertext = 768 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-1c ciphertext = 768 bytes")
ml_kem_512_ct_bytes().to_equal(768)
```

</details>

#### ITEM-1d shared secret = 32 bytes

- ITEM-1d shared secret = 32 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-1d shared secret = 32 bytes")
ml_kem_512_ss_bytes().to_equal(32)
```

</details>

### ML-KEM-512 parameter table (FIPS 203 §2.3 Table 2)

#### ITEM-2a k = 2

- ITEM-2a k = 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-2a k = 2")
ml_kem_k_512().to_equal(2)
```

</details>

#### ITEM-2b η1 = 3

- ITEM-2b η1 = 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-2b η1 = 3")
ml_kem_eta1_512().to_equal(3)
```

</details>

#### ITEM-2c η2 = 2

- ITEM-2c η2 = 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-2c η2 = 2")
ml_kem_eta2_512().to_equal(2)
```

</details>

#### ITEM-2d du = 10

- ITEM-2d du = 10


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-2d du = 10")
ml_kem_du_512().to_equal(10)
```

</details>

#### ITEM-2e dv = 4

- ITEM-2e dv = 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-2e dv = 4")
ml_kem_dv_512().to_equal(4)
```

</details>

#### ITEM-2f q = 3329 (shared)

- ITEM-2f q = 3329 (shared)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-2f q = 3329 (shared)")
ml_kem_q().to_equal(3329)
```

</details>

### ML-KEM-512 deterministic round-trip (top-level harness)

#### ITEM-3 KeyGen + Encaps + Decaps round-trip with d = z = m = 0^32

- ITEM-3 KeyGen + Encaps + Decaps round-trip with d = z = m = 0^32


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ITEM-3 KeyGen + Encaps + Decaps round-trip with d = z = m = 0^32")
# The actual round-trip computation runs at file load via
# `ml_kem_512_round_trip_check()`. This `it` block records the
# outcome flag; if loading succeeded with a wrong shared secret,
# the flag is 0 and this assertion fails.
ml_kem_512_round_trip_ok.to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/ml_kem_512_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ML-KEM-512 size invariants (FIPS 203 §8 Table 3), ML-KEM-512 parameter table (FIPS 203 §2.3 Table 2), ML-KEM-512 deterministic round-trip (top-level harness).
- ML-KEM-512 size invariants (FIPS 203 §8 Table 3)
- ML-KEM-512 parameter table (FIPS 203 §2.3 Table 2)
- ML-KEM-512 deterministic round-trip (top-level harness)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `14630db64c2c69fa22e856ff4538a1690116dd2bb6e3d6f001ce64758bd5667d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14630db64c2c69fa22e856ff4538a1690116dd2bb6e3d6f001ce64758bd5667d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14630db64c2c69fa22e856ff4538a1690116dd2bb6e3d6f001ce64758bd5667d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/ml_kem_512_kat_spec.spl
mirror: doc/06_spec/unit/lib/crypto/ml_kem_512_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/ml_kem_512_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/ml_kem_512_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/ml_kem_512_kat_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ITEM-1a ek = 800 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/ml_kem_512_kat_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ITEM-1b dk = 1632 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/ml_kem_512_kat_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ITEM-1c ciphertext = 768 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Sha224 Kat Specification

> Tests covering SHA-224 — FIPS 180-4 known-answer vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha224 Kat Specification

## Scenarios

### SHA-224 — FIPS 180-4 known-answer vectors

#### SHA-224(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SHA-224(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-224(\")
expect(_bytes_hex(sha224(_empty_bytes()))).to_equal(
    "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f"
)
```

</details>

#### SHA-224(\

- SHA-224(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-224(\")
expect(_bytes_hex(sha224(_abc_bytes()))).to_equal(
    "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7"
)
```

</details>

#### SHA-224 output length is 28 bytes

- SHA-224 output length is 28 bytes
   - Expected: sha224(_abc_bytes()).len() equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-224 output length is 28 bytes")
expect(sha224(_abc_bytes()).len()).to_equal(28)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/sha224_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHA-224 — FIPS 180-4 known-answer vectors.
- SHA-224 — FIPS 180-4 known-answer vectors

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2a24823829f0e72c97e5b7fa43a14337a55fddb094908ba9466de72df22c9d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2a24823829f0e72c97e5b7fa43a14337a55fddb094908ba9466de72df22c9d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2a24823829f0e72c97e5b7fa43a14337a55fddb094908ba9466de72df22c9d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/crypto/sha224_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/sha224_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/sha224_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/sha224_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/sha224_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/sha224_kat_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SHA-224(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/sha224_kat_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SHA-224(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/sha224_kat_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SHA-224 output length is 28 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

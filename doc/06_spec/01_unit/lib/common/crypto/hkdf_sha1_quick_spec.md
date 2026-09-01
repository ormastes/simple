# Hkdf Sha1 Quick Specification

> Tests covering hkdf sha1 timing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hkdf Sha1 Quick Specification

## Scenarios

### hkdf sha1 timing

#### extract is fast

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extract is fast
   - Expected: prk.len() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extract is fast")
val prk = hkdf_extract_sha1(_salt(), _ikm())
expect(prk.len()).to_equal(20)
```

</details>

#### expand L=42 is fast enough

- expand L=42 is fast enough
   - Expected: okm.len() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expand L=42 is fast enough")
val prk = hkdf_extract_sha1(_salt(), _ikm())
val okm = hkdf_expand_sha1(prk, _info(), 42)
expect(okm.len()).to_equal(42)
expect(bytes_to_hex(okm)).to_equal(
    "085a01ea1b10f36933068b56efa5ad81a4f14b822f5b091568a9cdd4f155fda2c22e422478d305f3f896"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hkdf sha1 timing.
- hkdf sha1 timing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `fde860cb4d15ed00d5aa7b7d782e3ec4568c02767a7795abd39f5c0d2ed1ed2d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fde860cb4d15ed00d5aa7b7d782e3ec4568c02767a7795abd39f5c0d2ed1ed2d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fde860cb4d15ed00d5aa7b7d782e3ec4568c02767a7795abd39f5c0d2ed1ed2d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extract is fast' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expand L=42 is fast enough' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Tiger Kat Specification

> Tests covering Tiger/192 -- Anderson+Biham 1996 known-answer vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tiger Kat Specification

## Scenarios

### Tiger/192 -- Anderson+Biham 1996 known-answer vectors

#### Tiger(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Tiger(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Tiger(\")
expect(_bytes_hex(tiger192(_empty_bytes()))).to_equal(
    "3293ac630c13f0245f92bbb1766e16167a4e58492dde73f3"
)
```

</details>

#### Tiger(\

- Tiger(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Tiger(\")
expect(_bytes_hex(tiger192(_a_bytes()))).to_equal(
    "77befbef2e7ef8ab2ec8f93bf587a7fc613e247f5f247809"
)
```

</details>

#### Tiger(\

- Tiger(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Tiger(\")
expect(_bytes_hex(tiger192(_abc_bytes()))).to_equal(
    "2aab1484e8c158f2bfb8c5ff41b57a525129131c957b5f93"
)
```

</details>

#### Tiger(\

- Tiger(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Tiger(\")
expect(_bytes_hex(tiger192(_tiger_bytes()))).to_equal(
    "dd00230799f5009fec6debc838bb6a27df2b9d6f110c7937"
)
```

</details>

#### Tiger/192 output length is 24 bytes

- Tiger/192 output length is 24 bytes
   - Expected: tiger192(_abc_bytes()).len() equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Tiger/192 output length is 24 bytes")
expect(tiger192(_abc_bytes()).len()).to_equal(24)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/tiger_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Tiger/192 -- Anderson+Biham 1996 known-answer vectors.
- Tiger/192 -- Anderson+Biham 1996 known-answer vectors

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

- Canonical SPipe generation for source `ae4d5c893803d59b357cefb2dc1367c0753758b322f1c9c0f109a07868654b5d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae4d5c893803d59b357cefb2dc1367c0753758b322f1c9c0f109a07868654b5d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae4d5c893803d59b357cefb2dc1367c0753758b322f1c9c0f109a07868654b5d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/crypto/tiger_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/tiger_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/tiger_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/tiger_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/tiger_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/tiger_kat_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Tiger(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/tiger_kat_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Tiger(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/tiger_kat_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Tiger(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

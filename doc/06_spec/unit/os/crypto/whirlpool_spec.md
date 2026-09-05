# Whirlpool Specification

> Tests covering Whirlpool ISO/IEC 10118-3 known-answer vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Whirlpool Specification

## Scenarios

### Whirlpool ISO/IEC 10118-3 known-answer vectors

#### whirlpool(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- whirlpool(\
   - Expected: _whirlpool_empty_first8() equals `19fa61d75522a466`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whirlpool(\")
expect(_whirlpool_empty_first8()).to_equal("19fa61d75522a466")
```

</details>

#### whirlpool(\

- whirlpool(\
   - Expected: _whirlpool_a_first8() equals `8aca2602792aec6f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whirlpool(\")
expect(_whirlpool_a_first8()).to_equal("8aca2602792aec6f")
```

</details>

#### whirlpool output length is 64 bytes

- whirlpool output length is 64 bytes
   - Expected: _whirlpool_empty_len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whirlpool output length is 64 bytes")
expect(_whirlpool_empty_len()).to_equal(64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/whirlpool_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Whirlpool ISO/IEC 10118-3 known-answer vectors.
- Whirlpool ISO/IEC 10118-3 known-answer vectors

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

- Canonical SPipe generation for source `ce6f7241488260037a2f016966161bfbd0e6d59b21cae13ff8c6fcd2fce8d266`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce6f7241488260037a2f016966161bfbd0e6d59b21cae13ff8c6fcd2fce8d266`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce6f7241488260037a2f016966161bfbd0e6d59b21cae13ff8c6fcd2fce8d266`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/crypto/whirlpool_spec.spl
mirror: doc/06_spec/unit/os/crypto/whirlpool_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/whirlpool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/whirlpool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/whirlpool_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/whirlpool_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'whirlpool(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/whirlpool_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'whirlpool(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/whirlpool_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'whirlpool output length is 64 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

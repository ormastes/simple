# Strings Specification

> Tests covering strings tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Strings Specification

## Scenarios

### strings tool

#### printable detection

#### identifies printable ASCII range

- identifies printable ASCII range
   - Expected: is_printable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies printable ASCII range")
val code = 65  # 'A'
val is_printable = code >= 32 and code < 127
expect(is_printable).to_equal(true)
```

</details>

#### rejects control characters

- rejects control characters
   - Expected: is_printable is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects control characters")
val code = 0
val is_printable = code >= 32 and code < 127
expect(is_printable).to_equal(false)
```

</details>

#### minimum length

#### filters short strings

- filters short strings
   - Expected: s.len() < min_len is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters short strings")
val s = "ab"
val min_len = 4
expect(s.len() < min_len).to_equal(true)
```

</details>

#### keeps long enough strings

- keeps long enough strings
   - Expected: s.len() >= min_len is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps long enough strings")
val s = "hello"
val min_len = 4
expect(s.len() >= min_len).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/shell/strings_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering strings tool.
- strings tool

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

- Canonical SPipe generation for source `5db0a4b01ab672485a97b0d4abf212a9aeb24f64e38a0b2d3f0effddf4622938`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5db0a4b01ab672485a97b0d4abf212a9aeb24f64e38a0b2d3f0effddf4622938`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5db0a4b01ab672485a97b0d4abf212a9aeb24f64e38a0b2d3f0effddf4622938`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/tools/shell/strings_spec.spl
mirror: doc/06_spec/unit/tools/shell/strings_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/shell/strings_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/shell/strings_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/shell/strings_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies printable ASCII range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/strings_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects control characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/strings_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters short strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

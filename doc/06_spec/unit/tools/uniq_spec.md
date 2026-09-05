# Uniq Specification

> Tests covering uniq tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Uniq Specification

## Scenarios

### uniq tool

#### line comparison

#### detects equal lines

- detects equal lines
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects equal lines")
val result = lines_equal("hello", "hello", false)
expect(result).to_equal(true)
```

</details>

#### detects different lines

- detects different lines
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects different lines")
val result = lines_equal("hello", "world", false)
expect(result).to_equal(false)
```

</details>

#### compares case-insensitively

- compares case-insensitively
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares case-insensitively")
val result = lines_equal("Hello", "hello", true)
expect(result).to_equal(true)
```

</details>

#### rejects different lines case-insensitively

- rejects different lines case-insensitively
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects different lines case-insensitively")
val result = lines_equal("Hello", "World", true)
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/uniq_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering uniq tool.
- uniq tool

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

- Canonical SPipe generation for source `40aeec1d82de1d080c68efd5c34baf8ed429adfd27653aa183bc3b9ec19d86cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40aeec1d82de1d080c68efd5c34baf8ed429adfd27653aa183bc3b9ec19d86cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40aeec1d82de1d080c68efd5c34baf8ed429adfd27653aa183bc3b9ec19d86cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/tools/uniq_spec.spl
mirror: doc/06_spec/unit/tools/uniq_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/uniq_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/uniq_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/uniq_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects equal lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/uniq_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects different lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/uniq_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares case-insensitively' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Validation Utils Specification

> Tests covering Validation Utilities, Number Validation, String Validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Validation Utils Specification

## Scenarios

### Validation Utilities

### Number Validation

#### is_positive works

- is_positive works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_positive works")
expect is_positive(5)
expect not is_positive(0)
expect not is_positive(-5)
```

</details>

#### is_negative works

- is_negative works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_negative works")
expect is_negative(-5)
expect not is_negative(0)
expect not is_negative(5)
```

</details>

#### is_non_negative works

- is_non_negative works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_non_negative works")
expect is_non_negative(0)
expect is_non_negative(5)
expect not is_non_negative(-5)
```

</details>

#### is_in_range works

- is_in_range works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_in_range works")
expect is_in_range(x=5, min_val=0, max_val=10)
expect not is_in_range(x=-1, min_val=0, max_val=10)
expect not is_in_range(x=11, min_val=0, max_val=10)
```

</details>

### String Validation

#### is_not_empty works

- is_not_empty works


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_not_empty works")
expect is_not_empty("hello")
expect not is_not_empty("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/validation_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Validation Utilities, Number Validation, String Validation.
- Validation Utilities
- Number Validation
- String Validation

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

- Canonical SPipe generation for source `eac9b3d64569e63c9a44def25d0f71e81f69de24cb1e18933be49595c756f935`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eac9b3d64569e63c9a44def25d0f71e81f69de24cb1e18933be49595c756f935`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eac9b3d64569e63c9a44def25d0f71e81f69de24cb1e18933be49595c756f935`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/validation_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/validation_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/validation_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/validation_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/validation_utils_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_positive works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/validation_utils_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_negative works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/validation_utils_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_non_negative works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

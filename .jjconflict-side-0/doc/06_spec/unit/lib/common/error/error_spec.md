# Error Specification

> Tests covering std.error.error.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Specification

## Scenarios

### std.error.error

#### rt_error_value

#### returns 27 (RT_ERROR = (SPECIAL_ERROR=3 << 3) | TAG_SPECIAL=3)

- returns 27 (RT_ERROR = (SPECIAL_ERROR=3 << 3) | TAG_SPECIAL=3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 27 (RT_ERROR = (SPECIAL_ERROR=3 << 3) | TAG_SPECIAL=3)")
val v = rt_error_value()
expect v == 27
```

</details>

#### is consistent across calls

- is consistent across calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is consistent across calls")
val a = rt_error_value()
val b = rt_error_value()
expect a == b
```

</details>

#### rt_method_not_found

#### returns RT_ERROR value (27)

- returns RT_ERROR value (27)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns RT_ERROR value (27)")
val res = rt_method_not_found("MyType", "some_method")
expect res == 27
```

</details>

#### returns RT_ERROR for empty strings

- returns RT_ERROR for empty strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns RT_ERROR for empty strings")
val res = rt_method_not_found("", "")
expect res == 27
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/error/error_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.error.error.
- std.error.error

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

- Canonical SPipe generation for source `79240912b699eb166630a288905e2638e3e38b95c491fe533e6b85ef701a1df4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79240912b699eb166630a288905e2638e3e38b95c491fe533e6b85ef701a1df4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79240912b699eb166630a288905e2638e3e38b95c491fe533e6b85ef701a1df4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/error/error_spec.spl
mirror: doc/06_spec/unit/lib/common/error/error_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/error/error_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/error/error_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/error/error_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 27 (RT_ERROR = (SPECIAL_ERROR=3 << 3) | TAG_SPECIAL=3)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/error/error_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is consistent across calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/error/error_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns RT_ERROR value (27)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

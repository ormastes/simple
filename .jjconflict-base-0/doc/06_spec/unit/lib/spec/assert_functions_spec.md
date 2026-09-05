# Assert Functions Specification

> Tests covering standalone assert functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assert Functions Specification

## Scenarios

### standalone assert functions

#### assert_true passes for true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assert_true passes for true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_true passes for true")
assert_true(true)
```

</details>

#### assert_false passes for false

- assert_false passes for false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_false passes for false")
assert_false(false)
```

</details>

#### assert_equal passes for equal integers

- assert_equal passes for equal integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_equal passes for equal integers")
assert_equal(42, 42)
```

</details>

#### assert_equal passes for equal strings

- assert_equal passes for equal strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_equal passes for equal strings")
assert_equal("hello", "hello")
```

</details>

#### assert_not_equal passes for different values

- assert_not_equal passes for different values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_not_equal passes for different values")
assert_not_equal(1, 2)
```

</details>

#### assert_contains passes when substring is present

- assert_contains passes when substring is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_contains passes when substring is present")
assert_contains("hello world", "world")
```

</details>

#### assert_nil passes for nil

- assert_nil passes for nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_nil passes for nil")
assert_nil(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/spec/assert_functions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering standalone assert functions.
- standalone assert functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `2bc312bde9d2ce07a8e8ff1f11a3db51da8738650a0c8b2c8b23b9cafca95c9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2bc312bde9d2ce07a8e8ff1f11a3db51da8738650a0c8b2c8b23b9cafca95c9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2bc312bde9d2ce07a8e8ff1f11a3db51da8738650a0c8b2c8b23b9cafca95c9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/spec/assert_functions_spec.spl
mirror: doc/06_spec/unit/lib/spec/assert_functions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/spec/assert_functions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/spec/assert_functions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/spec/assert_functions_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assert_true passes for true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/spec/assert_functions_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assert_false passes for false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/spec/assert_functions_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assert_equal passes for equal integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Multiline Bool Specification

> Tests covering Multiline Boolean Lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multiline Bool Specification

## Scenarios

### Multiline Boolean Lint

#### multiline if with trailing boolean operator

#### flags multiline if with trailing and (BOOL001)

- flags multiline if with trailing and (BOOL001)
   - Expected: has_bool001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags multiline if with trailing and (BOOL001)")
val code = "fn test(a: bool, b: bool):\n    if a and\n       b:\n        print \"both true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(true)
```

</details>

#### flags multiline if with trailing or

- flags multiline if with trailing or
   - Expected: has_bool001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags multiline if with trailing or")
val code = "fn test(x: bool, y: bool):\n    if x or\n       y:\n        print \"either true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(true)
```

</details>

#### single-line boolean

#### does not flag single-line if with and

- does not flag single-line if with and
   - Expected: has_bool001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag single-line if with and")
val code = "fn test(a: bool, b: bool):\n    if a and b:\n        print \"both true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(false)
```

</details>

#### does not flag single-line if with or

- does not flag single-line if with or
   - Expected: has_bool001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag single-line if with or")
val code = "fn test(x: bool, y: bool):\n    if x or y:\n        print \"either true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(false)
```

</details>

#### parenthesized multiline boolean

#### does not flag parenthesized multiline boolean

- does not flag parenthesized multiline boolean
   - Expected: has_bool001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag parenthesized multiline boolean")
val code = "fn test(a: bool, b: bool):\n    if (a and\n        b):\n        print \"both true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(false)
```

</details>

#### does not flag parenthesized multiline or

- does not flag parenthesized multiline or
   - Expected: has_bool001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag parenthesized multiline or")
val code = "fn test(x: bool, y: bool):\n    if (x or\n        y):\n        print \"either true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/multiline_bool_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Multiline Boolean Lint.
- Multiline Boolean Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `b77ce59fa46b42ba53eb2abbada2ed1fee7798f4717b4aeb93cd860ac4ad12c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b77ce59fa46b42ba53eb2abbada2ed1fee7798f4717b4aeb93cd860ac4ad12c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b77ce59fa46b42ba53eb2abbada2ed1fee7798f4717b4aeb93cd860ac4ad12c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/lint/multiline_bool_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/lint/multiline_bool_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/lint/multiline_bool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/lint/multiline_bool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/lint/multiline_bool_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags multiline if with trailing and (BOOL001)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/multiline_bool_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags multiline if with trailing or' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/multiline_bool_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag single-line if with and' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

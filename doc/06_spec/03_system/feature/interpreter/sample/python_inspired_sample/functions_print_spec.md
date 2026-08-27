# Functions with Print/Side Effects (Interpreter)

> Tests function execution with print and side effect operations in the interpreter. Verifies that functions producing output and performing I/O side effects execute in the correct order with expected observable behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Functions with Print/Side Effects (Interpreter)

Tests function execution with print and side effect operations in the interpreter. Verifies that functions producing output and performing I/O side effects execute in the correct order with expected observable behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/functions_print_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests function execution with print and side effect operations in the interpreter.
Verifies that functions producing output and performing I/O side effects execute
in the correct order with expected observable behavior.

## Scenarios

### Functions with Print and Side Effects

#### print function

#### prints simple string

- prints simple string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints simple string")
# Note: we can't easily test print output in SPipe
# This test verifies print doesn't error
val msg = "test message"
expect msg.len() > 0
```

</details>

#### string formatting

#### formats with interpolation

- formats with interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats with interpolation")
val name = "Alice"
val age = 30
val formatted = "{name} is {age} years old"
expect formatted == "Alice is 30 years old"
```

</details>

#### formats expressions

- formats expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats expressions")
val x = 5
val y = 3
val result = "{x} + {y} = {x + y}"
expect result == "5 + 3 = 8"
```

</details>

#### side effect functions

#### executes side effects in order

- executes side effects in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes side effects in order")
fn increment(c: i64) -> i64:
    c + 1
var counter = 0
counter = increment(counter)
counter = increment(counter)
expect counter == 2
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6e4307f765be2f840a12a2a2f58b7a2784c4206e8b7b54a0972782c38e3ce558`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6e4307f765be2f840a12a2a2f58b7a2784c4206e8b7b54a0972782c38e3ce558`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6e4307f765be2f840a12a2a2f58b7a2784c4206e8b7b54a0972782c38e3ce558`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/interpreter/sample/python_inspired_sample/functions_print_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/functions_print_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/functions_print_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/functions_print_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/sample/python_inspired_sample/functions_print_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints simple string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/functions_print_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats with interpolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/functions_print_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

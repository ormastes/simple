# Control Flow (Python-Inspired Sample)

> Tests compilation of control flow constructs inspired by Python including if/else, for loops, while loops, and match expressions. Verifies that indentation-based control flow compiles correctly through the native pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Control Flow (Python-Inspired Sample)

Tests compilation of control flow constructs inspired by Python including if/else, for loops, while loops, and match expressions. Verifies that indentation-based control flow compiles correctly through the native pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/control_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of control flow constructs inspired by Python including if/else,
for loops, while loops, and match expressions. Verifies that indentation-based
control flow compiles correctly through the native pipeline.

## Scenarios

### Control Flow

#### if/else

#### executes if branch when true

- executes if branch when true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes if branch when true")
val x = 10
var result = ""
if x > 5:
    result = "big"
else:
    result = "small"
expect result == "big"
```

</details>

#### executes else branch when false

- executes else branch when false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes else branch when false")
val x = 3
var result = ""
if x > 5:
    result = "big"
else:
    result = "small"
expect result == "small"
```

</details>

#### for loops

#### iterates over range

- iterates over range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates over range")
var sum = 0
for i in 0..5:
    sum = sum + i
expect sum == 10
```

</details>

#### iterates over list

- iterates over list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates over list")
val items = ["a", "b", "c"]
var count = 0
for item in items:
    count = count + 1
expect count == 3
```

</details>

#### while loops

<details>
<summary>Advanced: loops while condition is true</summary>

#### loops while condition is true

- loops while condition is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loops while condition is true")
var i = 0
var sum = 0
while i < 5:
    sum = sum + i
    i = i + 1
expect sum == 10
```

</details>


</details>

#### match expressions

#### matches literal values

- matches literal values


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches literal values")
val x = 2
val result = match x:
    case 1:
        "one"
    case 2:
        "two"
    case _:
        "other"
expect result == "two"
```

</details>

#### matches with guards

- matches with guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches with guards")
val n = 15
val category = match n:
    case x if x > 10:
        "large"
    case x if x > 0:
        "small"
    case _:
        "non-positive"
expect category == "large"
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `708d71f2cf61e279f9c15254a62883ac89dfe0d1552d4e0b79ebf5a36d346665`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `708d71f2cf61e279f9c15254a62883ac89dfe0d1552d4e0b79ebf5a36d346665`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `708d71f2cf61e279f9c15254a62883ac89dfe0d1552d4e0b79ebf5a36d346665`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/compiler/sample/python_inspired_sample/control_flow_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/control_flow_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/control_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/control_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/sample/python_inspired_sample/control_flow_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes if branch when true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/control_flow_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes else branch when false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/control_flow_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'iterates over range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

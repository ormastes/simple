# Control Flow Patterns (Interpreter Sample)

> Tests Python-inspired control flow patterns in the interpreter including if/elif/else chains, while loops with break/continue, and for-in iteration. Verifies that indentation-based control flow works correctly in interpreted mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Control Flow Patterns (Interpreter Sample)

Tests Python-inspired control flow patterns in the interpreter including if/elif/else chains, while loops with break/continue, and for-in iteration. Verifies that indentation-based control flow works correctly in interpreted mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/control_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests Python-inspired control flow patterns in the interpreter including if/elif/else
chains, while loops with break/continue, and for-in iteration. Verifies that
indentation-based control flow works correctly in interpreted mode.

## Scenarios

### Control Flow

#### if expressions

#### evaluates then branch when true

- evaluates then branch when true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates then branch when true")
val result = if true: "yes" else: "no"
expect result == "yes"
```

</details>

#### evaluates else branch when false

- evaluates else branch when false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates else branch when false")
val result = if false: "yes" else: "no"
expect result == "no"
```

</details>

#### chains elif conditions

- chains elif conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains elif conditions")
fn classify(x: i64) -> text:
    if x > 0:
        "positive"
    elif x < 0:
        "negative"
    else:
        "zero"
expect classify(5) == "positive"
expect classify(-5) == "negative"
expect classify(0) == "zero"
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
val items = [1, 2, 3]
var total = 0
for item in items:
    total = total + item
expect total == 6
```

</details>

#### while loops

<details>
<summary>Advanced: loops while condition true</summary>

#### loops while condition true

- loops while condition true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loops while condition true")
var count = 0
while count < 3:
    count = count + 1
expect count == 3
```

</details>


</details>

#### match expressions

#### matches literal pattern

- matches literal pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches literal pattern")
fn describe(x: i64) -> text:
    match x:
        case 0:
            "zero"
        case 1:
            "one"
        case _:
            "other"
expect describe(0) == "zero"
expect describe(1) == "one"
expect describe(99) == "other"
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

- Canonical SPipe generation for source `9df5a4f43e56984748935eb395b684dbfacabeeb036c1623a86acffe7adad1eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9df5a4f43e56984748935eb395b684dbfacabeeb036c1623a86acffe7adad1eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9df5a4f43e56984748935eb395b684dbfacabeeb036c1623a86acffe7adad1eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/interpreter/sample/python_inspired_sample/control_flow_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/control_flow_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/control_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/control_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/sample/python_inspired_sample/control_flow_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates then branch when true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/control_flow_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates else branch when false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/control_flow_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chains elif conditions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

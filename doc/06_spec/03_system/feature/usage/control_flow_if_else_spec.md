# Control Flow - If/Else Specification

> Tests for conditional control flow using if/else statements.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Control Flow - If/Else Specification

Tests for conditional control flow using if/else statements.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1001 |
| Category | Language |
| Status | In Progress |
| Source | `test/03_system/feature/usage/control_flow_if_else_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for conditional control flow using if/else statements.
Verifies correct evaluation of conditions and execution of appropriate branches.

## Scenarios

### Control Flow - If/Else

#### basic if statements

#### executes if body when condition is true

- executes if body when condition is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes if body when condition is true")
val x = 5
var result = 0
if x > 0:
    result = 10
expect result == 10
```

</details>

#### skips if body when condition is false

- skips if body when condition is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips if body when condition is false")
val x = -5
var result = 0
if x > 0:
    result = 10
expect result == 0
```

</details>

#### if-else statements

#### executes if body when condition is true

- executes if body when condition is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes if body when condition is true")
val x = 10
var result = ""
if x > 5:
    result = "greater"
else:
    result = "less"
expect result == "greater"
```

</details>

#### executes else body when condition is false

- executes else body when condition is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes else body when condition is false")
val x = 3
var result = ""
if x > 5:
    result = "greater"
else:
    result = "less"
expect result == "less"
```

</details>

#### nested if statements

#### handles nested if statements

- handles nested if statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles nested if statements")
val x = 10
val y = 20
var result = 0
if x > 5:
    if y > 15:
        result = 1
expect result == 1
```

</details>

#### handles nested if-else

- handles nested if-else


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles nested if-else")
val x = 3
val y = 20
var result = 0
if x > 5:
    result = 1
else:
    if y > 15:
        result = 2
expect result == 2
```

</details>

#### if-else-if chains

#### evaluates first matching condition

- evaluates first matching condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates first matching condition")
val x = 15
var result = ""
if x < 10:
    result = "low"
else:
    if x < 20:
        result = "medium"
    else:
        result = "high"
expect result == "medium"
```

</details>

#### executes final else when no conditions match

- executes final else when no conditions match


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes final else when no conditions match")
val x = 100
var result = ""
if x < 10:
    result = "low"
else:
    if x < 20:
        result = "medium"
    else:
        result = "high"
expect result == "high"
```

</details>

#### if with boolean expressions

#### evaluates AND conditions

- evaluates AND conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates AND conditions")
val a = 5
val b = 10
var result = false
if a > 0 and b > 0:
    result = true
expect result == true
```

</details>

#### evaluates OR conditions

- evaluates OR conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates OR conditions")
val a = -5
val b = 10
var result = false
if a > 0 or b > 0:
    result = true
expect result == true
```

</details>

#### evaluates NOT conditions

- evaluates NOT conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates NOT conditions")
val x = 5
var result = false
if not (x < 0):
    result = true
expect result == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `20b5e421438788b063bc0af04c4b44857601426c4ed79a05be2b847b587daea7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20b5e421438788b063bc0af04c4b44857601426c4ed79a05be2b847b587daea7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20b5e421438788b063bc0af04c4b44857601426c4ed79a05be2b847b587daea7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/control_flow_if_else_spec.spl
mirror: doc/06_spec/03_system/feature/usage/control_flow_if_else_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/control_flow_if_else_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/control_flow_if_else_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/control_flow_if_else_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes if body when condition is true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/control_flow_if_else_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips if body when condition is false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/control_flow_if_else_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes if body when condition is true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

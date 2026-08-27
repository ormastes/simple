# Control Flow (Interpreter)

> Tests control flow constructs in the interpreter including if/else, match, for/while loops, and early returns. Verifies that branching, iteration, and loop control statements execute with correct semantics in interpreted mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Control Flow (Interpreter)

Tests control flow constructs in the interpreter including if/else, match, for/while loops, and early returns. Verifies that branching, iteration, and loop control statements execute with correct semantics in interpreted mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/control_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests control flow constructs in the interpreter including if/else, match, for/while
loops, and early returns. Verifies that branching, iteration, and loop control
statements execute with correct semantics in interpreted mode.

## Scenarios

### eval_for

#### iterable evaluation

<details>
<summary>Advanced: evaluates iterable before loop</summary>

#### evaluates iterable before loop

- evaluates iterable before loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates iterable before loop")
var result = 0
val items = [1, 2, 3]
for x in items:
    result = result + x
expect result == 6
```

</details>


</details>

#### evaluates range expression

- evaluates range expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates range expression")
var sum = 0
for i in 1..5:
    sum = sum + i
expect sum == 10
```

</details>

#### loop variable scope

<details>
<summary>Advanced: creates new scope for loop variable</summary>

#### creates new scope for loop variable

- creates new scope for loop variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates new scope for loop variable")
val x = 100
for x in [1, 2, 3]:
    pass
expect x == 100
```

</details>


</details>

<details>
<summary>Advanced: binds loop variable for each iteration</summary>

#### binds loop variable for each iteration

- binds loop variable for each iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds loop variable for each iteration")
var last = 0
for i in [5, 10, 15]:
    last = i
expect last == 15
```

</details>


</details>

#### control flow signals

#### handles break with value

- handles break with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles break with value")
var count = 0
for i in 0..10:
    count = count + 1
    if i == 5:
        break
expect count == 6
```

</details>

#### handles continue signal

- handles continue signal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles continue signal")
var sum = 0
for i in 0..5:
    if i == 2:
        continue
    sum = sum + i
expect sum == 8
```

</details>

### eval_while

#### condition evaluation

#### checks condition before each iteration

- checks condition before each iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks condition before each iteration")
var i = 0
var count = 0
while i < 3:
    count = count + 1
    i = i + 1
expect count == 3
```

</details>

#### does not execute body if condition is false

- does not execute body if condition is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not execute body if condition is false")
var executed = false
while false:
    executed = true
expect not executed
```

</details>

#### control flow signals

#### handles continue signal

- handles continue signal


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles continue signal")
var sum = 0
var i = 0
while i < 5:
    i = i + 1
    if i == 3:
        continue
    sum = sum + i
expect sum == 12
```

</details>

#### handles break signal

- handles break signal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles break signal")
var count = 0
while true:
    count = count + 1
    if count == 5:
        break
expect count == 5
```

</details>

### eval_loop

#### break signal

#### breaks on Break signal

- breaks on Break signal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("breaks on Break signal")
var iterations = 0
loop:
    iterations = iterations + 1
    if iterations >= 3:
        break
expect iterations == 3
```

</details>

#### can break with computed condition

- can break with computed condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can break with computed condition")
var n = 10
loop:
    n = n - 1
    if n == 0:
        break
expect n == 0
```

</details>

### eval_if

#### condition evaluation

#### evaluates true condition

- evaluates true condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates true condition")
val result = if true: 1 else: 0
expect result == 1
```

</details>

#### evaluates false condition

- evaluates false condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates false condition")
val result = if false: 1 else: 0
expect result == 0
```

</details>

#### evaluates comparison expression

- evaluates comparison expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates comparison expression")
val x = 10
val result = if x > 5: 1 else: 0
expect result == 1
```

</details>

#### branch execution

#### executes then branch when true

- executes then branch when true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes then branch when true")
var executed = "none"
if true:
    executed = "then"
else:
    executed = "else"
expect executed == "then"
```

</details>

#### executes else branch when false

- executes else branch when false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes else branch when false")
var executed = "none"
if false:
    executed = "then"
else:
    executed = "else"
expect executed == "else"
```

</details>

### eval_match

#### tuple matching

#### matches tuple and binds variables

- matches tuple and binds variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches tuple and binds variables")
val t = (1, 2)
val result = match t:
    case (1, x): x * 10
    case _: 0
expect result == 20
```

</details>

#### uses wildcard for unmatched patterns

- uses wildcard for unmatched patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses wildcard for unmatched patterns")
val t = (5, 5)
val result = match t:
    case (1, x): x
    case _: 99
expect result == 99
```

</details>

#### array matching

#### matches array and binds elements

- matches array and binds elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches array and binds elements")
val arr = [5, 10]
val result = match arr:
    case [a, b]: a + b
    case _: 0
expect result == 15
```

</details>

#### handles array length mismatch

- handles array length mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles array length mismatch")
val arr = [1, 2, 3]
val result = match arr:
    case [a, b]: a + b
    case _: -1
expect result == -1
```

</details>

### Control Flow Integration

#### nests for inside while

- nests for inside while


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nests for inside while")
var sum = 0
var outer = 0
while outer < 2:
    for i in 0..3:
        sum = sum + 1
    outer = outer + 1
expect sum == 6
```

</details>

#### nests if inside for

- nests if inside for


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nests if inside for")
var evens = 0
for i in 0..10:
    if i % 2 == 0:
        evens = evens + 1
expect evens == 5
```

</details>

#### combines match with for

- combines match with for


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines match with for")
var sum = 0
val items = [(1, 10), (2, 20), (3, 30)]
for item in items:
    val add = match item:
        case (1, x): x
        case (2, x): x * 2
        case _: 0
    sum = sum + add
expect sum == 50
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `284b26f7a44a0ee4ee55802b93566803574d5be16f15384c44082bb7c33e1a4e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `284b26f7a44a0ee4ee55802b93566803574d5be16f15384c44082bb7c33e1a4e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `284b26f7a44a0ee4ee55802b93566803574d5be16f15384c44082bb7c33e1a4e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/feature/interpreter/control_flow_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/control_flow_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/control_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/control_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/control_flow_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates iterable before loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/control_flow_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates range expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/control_flow_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates new scope for loop variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/control_flow_spec.spl:220:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can break with computed condition' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

# Spipe System Test Specification

> Tests covering SPipe - Basic Assertions, SPipe - Variables and Computation, SPipe - Data Structures, SPipe - Control Flow, SPipe - Function Calls, SPipe - Context Blocks, SPipe - Integration Test, SPipe - Enumerations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spipe System Test Specification

## Scenarios

### SPipe - Basic Assertions

#### passes with true assertion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes with true assertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes with true assertion")
expect true
```

</details>

#### passes with equality check

- passes with equality check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes with equality check")
expect 2 + 2 == 4
```

</details>

#### passes with string equality

- passes with string equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes with string equality")
expect "hello" == "hello"
```

</details>

#### passes with array length

- passes with array length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes with array length")
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

### SPipe - Variables and Computation

#### evaluates arithmetic correctly

- evaluates arithmetic correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates arithmetic correctly")
val x = 10
val y = 20
val z = x + y
expect z == 30
```

</details>

#### works with strings

- works with strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with strings")
val name = "Alice"
expect name.len() == 5
```

</details>

#### works with arrays

- works with arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with arrays")
val numbers = [1, 2, 3, 4, 5]
expect numbers.len() == 5
expect numbers[0] == 1
expect numbers[4] == 5
```

</details>

### SPipe - Data Structures

#### handles simple classes

- handles simple classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles simple classes")
class Point:
    x: i32
    y: i32

val p = Point(x: 10, y: 20)
expect p.x == 10
expect p.y == 20
```

</details>

#### handles arrays of classes

- handles arrays of classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles arrays of classes")
class Item:
    name: text
    count: i32

var items: [Item] = []
items.push(Item(name: "apple", count: 5))
items.push(Item(name: "banana", count: 3))

expect items.len() == 2
expect items[0].count == 5
```

</details>

### SPipe - Control Flow

#### supports if statements

- supports if statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports if statements")
val x = 42
var result = 0
if x > 40:
    result = 1
else:
    result = 2
expect result == 1
```

</details>

<details>
<summary>Advanced: supports loops</summary>

#### supports loops

- supports loops


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports loops")
var sum = 0
for i in [1, 2, 3, 4, 5]:
    sum = sum + i
expect sum == 15
```

</details>


</details>

### SPipe - Function Calls

#### calls functions correctly

- calls functions correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls functions correctly")
val result = add(10, 20)
expect result == 30
```

</details>

#### chains function calls

- chains function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains function calls")
val result = add(multiply(2, 3), 4)
expect result == 10
```

</details>

### SPipe - Context Blocks

#### when testing math

#### adds numbers

- adds numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds numbers")
expect 5 + 3 == 8
```

</details>

#### subtracts numbers

- subtracts numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subtracts numbers")
expect 10 - 3 == 7
```

</details>

#### when testing strings

#### concatenates strings

- concatenates strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concatenates strings")
val s = "hello" + " " + "world"
expect s.len() == 11
```

</details>

### SPipe - Integration Test

#### runs complete calculator workflow

- runs complete calculator workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs complete calculator workflow")
val calc = Calculator(value: 0)
calc.add(10)
calc.add(5)
expect calc.get_value() == 15

calc.subtract(3)
expect calc.get_value() == 12
```

</details>

### SPipe - Enumerations

#### creates enum values

- creates enum values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates enum values")
val c = Color.Red
# Just verify it runs without error
expect true
```

</details>

#### uses enums in collections

- uses enums in collections


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses enums in collections")
var colors: [Color] = []
colors.push(Color.Red)
colors.push(Color.Blue)
expect colors.len() == 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/spipe_system_test_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe - Basic Assertions, SPipe - Variables and Computation, SPipe - Data Structures, SPipe - Control Flow, SPipe - Function Calls, SPipe - Context Blocks, SPipe - Integration Test, SPipe - Enumerations.
- SPipe - Basic Assertions
- SPipe - Variables and Computation
- SPipe - Data Structures
- SPipe - Control Flow
- SPipe - Function Calls
- SPipe - Context Blocks
- SPipe - Integration Test
- SPipe - Enumerations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `e5f59e7afac072498b9bdd6983e864789a3aa8faec4bc983c25c910b182a6e96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5f59e7afac072498b9bdd6983e864789a3aa8faec4bc983c25c910b182a6e96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5f59e7afac072498b9bdd6983e864789a3aa8faec4bc983c25c910b182a6e96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/spipe_system_test_spec.spl
mirror: doc/06_spec/unit/compiler/backend/spipe_system_test_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/spipe_system_test_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/spipe_system_test_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/spipe_system_test_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes with true assertion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/spipe_system_test_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes with equality check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/spipe_system_test_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes with string equality' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

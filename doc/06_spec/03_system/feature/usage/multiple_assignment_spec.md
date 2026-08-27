# Multiple Assignment (Destructuring) Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multiple Assignment (Destructuring) Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MULTIPLE-ASSIGNMENT |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/multiple_assignment_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Tuple destructuring
use std.spec.step

val (x, y) = get_point()
val (first, second, ...rest) = items

# Array destructuring
val [a, b, c] = triple

# Struct destructuring
val {name, age} = person
```

## Key Behaviors

- Pattern must match the structure of the value
- Variables are bound in the order they appear
- Wildcards `_` can ignore unwanted values
- Rest patterns `...rest` capture remaining elements

## Scenarios

### Multiple Assignment (Destructuring)

#### tuple destructuring

#### destructures a pair

- destructures a pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures a pair")
val pair = (10, 20)
val a = pair[0]
val b = pair[1]
expect a == 10
expect b == 20
```

</details>

#### destructures a triple

- destructures a triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures a triple")
val triple = (1, 2, 3)
val x = triple[0]
val y = triple[1]
val z = triple[2]
expect x == 1
expect y == 2
expect z == 3
```

</details>

#### uses destructured values in expressions

- uses destructured values in expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses destructured values in expressions")
val point = (3, 4)
val x = point[0]
val y = point[1]
val distance_squared = x * x + y * y
expect distance_squared == 25
```

</details>

#### destructures function return value

- destructures function return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures function return value")
fn get_coordinates() -> (i64, i64):
    (100, 200)
val _result = get_coordinates()
val x = _result[0]
val y = _result[1]
expect x == 100
expect y == 200
```

</details>

#### tuple destructuring with wildcards

#### ignores first element with wildcard

- ignores first element with wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores first element with wildcard")
val triple = (1, 2, 3)
# _ = triple[0]  # ignored
val b = triple[1]
val c = triple[2]
expect b == 2
expect c == 3
```

</details>

#### ignores middle element with wildcard

- ignores middle element with wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores middle element with wildcard")
val triple = (1, 2, 3)
val a = triple[0]
# _ = triple[1]  # ignored
val c = triple[2]
expect a == 1
expect c == 3
```

</details>

#### ignores last element with wildcard

- ignores last element with wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores last element with wildcard")
val triple = (1, 2, 3)
val a = triple[0]
val b = triple[1]
# _ = triple[2]  # ignored
expect a == 1
expect b == 2
```

</details>

#### ignores multiple elements

- ignores multiple elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores multiple elements")
val quad = (1, 2, 3, 4)
val a = quad[0]
# _ = quad[1]  # ignored
# _ = quad[2]  # ignored
val d = quad[3]
expect a == 1
expect d == 4
```

</details>

#### nested tuple destructuring

#### destructures nested tuples

- destructures nested tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures nested tuples")
val nested = ((1, 2), 3)
val _inner = nested[0]
val a = _inner[0]
val b = _inner[1]
val c = nested[1]
expect a == 1
expect b == 2
expect c == 3
```

</details>

#### destructures deeply nested tuples

- destructures deeply nested tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures deeply nested tuples")
val deep = (((1, 2), 3), 4)
val _outer = deep[0]
val _inner = _outer[0]
val a = _inner[0]
val b = _inner[1]
val c = _outer[1]
val d = deep[1]
expect a == 1
expect b == 2
expect c == 3
expect d == 4
```

</details>

#### array destructuring

#### destructures fixed-size array

- destructures fixed-size array


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures fixed-size array")
val arr = [10, 20, 30]
val a = arr[0]
val b = arr[1]
val c = arr[2]
expect a == 10
expect b == 20
expect c == 30
```

</details>

#### destructures with wildcard

- destructures with wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures with wildcard")
val arr = [1, 2, 3]
val x = arr[0]
# _ = arr[1]  # ignored
val z = arr[2]
expect x == 1
expect z == 3
```

</details>

#### mutable destructuring

#### creates mutable bindings

- creates mutable bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates mutable bindings")
val pair = (5, 10)
var a = pair[0]
var b = pair[1]
a = a + 1
b = b + 1
expect a == 6
expect b == 11
```

</details>

#### allows partial mutation

- allows partial mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows partial mutation")
val triple = (1, 2, 3)
var x = triple[0]
var y = triple[1]
var z = triple[2]
x = x * 10
expect x == 10
expect y == 2
expect z == 3
```

</details>

#### mixed type destructuring

#### destructures tuples with different types

- destructures tuples with different types


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures tuples with different types")
val mixed = ("hello", 42)
val name = mixed[0]
val count = mixed[1]
expect name == "hello"
expect count == 42
```

</details>

#### destructures nested mixed types

- destructures nested mixed types


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures nested mixed types")
val data = (("Alice", 30), true)
val _inner = data[0]
val name = _inner[0]
val age = _inner[1]
val active = data[1]
expect name == "Alice"
expect age == 30
expect active == true
```

</details>

#### destructuring in loops

<details>
<summary>Advanced: destructures in for loop</summary>

#### destructures in for loop

- destructures in for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures in for loop")
# Tuple destructuring inside for loop body is not supported
# in interpreter mode. Use indexed access instead.
val pairs = [(1, 2), (3, 4), (5, 6)]
fn sum_pairs(pairs) -> i64:
    var sum = 0
    for pair in pairs:
        sum = sum + pair[0] + pair[1]
    sum
expect sum_pairs(pairs) == 21
```

</details>


</details>

#### uses destructured values for computation

- uses destructured values for computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses destructured values for computation")
val points = [(0, 0), (3, 4), (6, 8)]
fn sum_points(points) -> i64:
    var total = 0
    for point in points:
        total = total + point[0] + point[1]
    total
expect sum_points(points) == 21
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `0925250c64244959c80c36d078b1c5d0189a7de4f97efbd48ae980d150629aa1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0925250c64244959c80c36d078b1c5d0189a7de4f97efbd48ae980d150629aa1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0925250c64244959c80c36d078b1c5d0189a7de4f97efbd48ae980d150629aa1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/multiple_assignment_spec.spl
mirror: doc/06_spec/03_system/feature/usage/multiple_assignment_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/multiple_assignment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/multiple_assignment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/multiple_assignment_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'destructures a pair' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/multiple_assignment_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'destructures a triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/multiple_assignment_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses destructured values in expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Array Type System and Operations

> Arrays are Simple's primary ordered collection type, supporting literal construction, positive and negative indexing, slicing with `start:end:step` notation, and a full suite of functional methods (`map`, `filter`, `reduce`, `all`, `join`, `sum`). This comprehensive spec covers eight aspects of array behavior: basic creation and queries, mutation via `push` and `concat`, functional transformations, Python-style slicing, negative indexing, the spread operator (`*`) for array merging, list comprehensions with optional filter clauses, and chained comparison expressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array Type System and Operations

Arrays are Simple's primary ordered collection type, supporting literal construction, positive and negative indexing, slicing with `start:end:step` notation, and a full suite of functional methods (`map`, `filter`, `reduce`, `all`, `join`, `sum`). This comprehensive spec covers eight aspects of array behavior: basic creation and queries, mutation via `push` and `concat`, functional transformations, Python-style slicing, negative indexing, the spread operator (`*`) for array merging, list comprehensions with optional filter clauses, and chained comparison expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-003 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/array_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Arrays are Simple's primary ordered collection type, supporting literal construction,
positive and negative indexing, slicing with `start:end:step` notation, and a full suite
of functional methods (`map`, `filter`, `reduce`, `all`, `join`, `sum`). This comprehensive
spec covers eight aspects of array behavior: basic creation and queries, mutation via `push`
and `concat`, functional transformations, Python-style slicing, negative indexing, the
spread operator (`*`) for array merging, list comprehensions with optional filter clauses,
and chained comparison expressions.

## Syntax

```simple
var arr = [1, 2, 3, 4, 5]
use std.spec.step

val doubled = arr.map(_1 * 2)
val sub = arr[1:4]
val evens = [x for x in arr if x % 2 == 0]
val merged = [*a, *b]
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Array Literal | `[1, 2, 3]` creates a dynamic array with inferred element type |
| Slicing | `arr[start:end:step]` extracts sub-arrays using Python-style notation |
| Spread Operator | `[*a, *b]` unpacks arrays inline to build a new merged array |
| List Comprehension | `[expr for x in iter if cond]` builds arrays with inline loops and filters |
| Functional Methods | `map`, `filter`, `reduce`, `all`, `join`, `sum` for declarative transforms |
| Negative Indexing | `arr[-1]` accesses elements from the end of the array |

## Scenarios

### Array Basics

#### array literals

#### creates array from literal

- creates array from literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates array from literal")
var arr = [1, 2, 3, 4, 5]
expect arr[2] == 3
```

</details>

#### gets array length

- gets array length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets array length")
var arr = [10, 20, 30]
expect arr.len() == 3
```

</details>

#### gets first and last elements

- gets first and last elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets first and last elements")
var arr = [5, 10, 15, 20]
expect arr.first() + arr.last() == 25
```

</details>

#### array queries

#### checks if array contains element

- checks if array contains element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if array contains element")
var arr = [1, 2, 3]
expect arr.contains(2)
```

</details>

#### checks if array is empty

- checks if array is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if array is empty")
var arr = []
expect arr.is_empty()
```

</details>

#### checks non-empty array

- checks non-empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks non-empty array")
var arr = [1]
expect not arr.is_empty()
```

</details>

### Array Modification

#### push and concat

#### pushes element to array

- pushes element to array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pushes element to array")
var arr = [1, 2, 3]
arr = arr.push(4)
expect arr[3] == 4
```

</details>

#### concatenates two arrays

- concatenates two arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("concatenates two arrays")
val a = [1, 2]
val b = [3, 4]
val c = a.concat(b)
expect c.len() == 4
```

</details>

#### reverse

#### reverses array

- reverses array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverses array")
var arr = [1, 2, 3]
val rev = arr.reverse()
expect rev[0] == 3
```

</details>

### Array Functional Methods

#### map

#### maps function over array

- maps function over array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps function over array")
var arr = [1, 2, 3]
val doubled = arr.map(_ * 2)
expect doubled[1] == 4
```

</details>

#### filter

#### filters array by predicate

- filters array by predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters array by predicate")
var arr = [1, 2, 3, 4, 5]
val evens = arr.filter(_ % 2 == 0)
expect evens.len() == 2
```

</details>

#### reduce

#### reduces array with accumulator

- reduces array with accumulator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reduces array with accumulator")
var arr = [1, 2, 3, 4, 5]
val sum = arr.reduce(0, \acc, x: acc + x)
expect sum == 15
```

</details>

#### all and any

#### checks all elements match predicate

- checks all elements match predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks all elements match predicate")
var arr = [2, 4, 6]
val all_even = arr.all(_1 % 2 == 0)
expect all_even
```

</details>

#### join

#### joins array elements with separator

- joins array elements with separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("joins array elements with separator")
var arr = [1, 2, 3]
val s = arr.join("-")
expect s == "1-2-3"
```

</details>

#### sum

#### sums numeric array

- sums numeric array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sums numeric array")
var arr = [1, 2, 3, 4, 5]
expect arr.sum() == 15
```

</details>

### Array Slicing

#### basic slicing

#### slices with start and end

- slices with start and end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with start and end")
var arr = [0, 1, 2, 3, 4, 5]
val sub = arr[1:4]
expect sub.len() == 3
```

</details>

#### slices from start index to end

- slices from start index to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices from start index to end")
var arr = [0, 1, 2, 3, 4]
val sub = arr[2:]
expect sub[0] == 2
```

</details>

#### slices from beginning to end index

- slices from beginning to end index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices from beginning to end index")
var arr = [0, 1, 2, 3, 4]
val sub = arr[:3]
expect sub.len() == 3
```

</details>

#### step slicing

#### slices with step

- slices with step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with step")
var arr = [0, 1, 2, 3, 4, 5, 6, 7]
val evens = arr[::2]
expect evens.len() == 4
```

</details>

### Negative Indexing

#### gets last element with -1

- gets last element with -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets last element with -1")
var arr = [10, 20, 30, 40, 50]
expect arr[-1] == 50
```

</details>

#### gets second from end with -2

- gets second from end with -2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets second from end with -2")
var arr = [1, 2, 3, 4, 5]
expect arr[-2] == 4
```

</details>

### Array Spread Operator

#### spreads arrays with *

- spreads arrays with *


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spreads arrays with *")
val a = [1, 2, 3]
val b = [4, 5]
val c = [*a, *b]
expect c.len() == 5
```

</details>

#### spreads array mixed with elements

- spreads array mixed with elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spreads array mixed with elements")
val a = [2, 3]
var arr = [1, *a, 4]
expect arr[2] == 3
```

</details>

### List Comprehension

#### creates list from comprehension

- creates list from comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates list from comprehension")
var arr = [1, 2, 3, 4, 5]
val doubled = [x * 2 for x in arr]
expect doubled[2] == 6
```

</details>

#### filters with comprehension condition

- filters with comprehension condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with comprehension condition")
var arr = [1, 2, 3, 4, 5, 6]
val evens = [x for x in arr if x % 2 == 0]
expect evens.len() == 3
```

</details>

#### creates squares with comprehension

- creates squares with comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates squares with comprehension")
val squares = [x * x for x in [1, 2, 3, 4]]
expect squares[3] == 16
```

</details>

### Chained Comparisons

#### evaluates basic chained comparison

- evaluates basic chained comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates basic chained comparison")
val x = 5
expect 0 < x and x < 10
```

</details>

#### evaluates false chained comparison

- evaluates false chained comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates false chained comparison")
val x = 15
expect not (0 < x and x < 10)
```

</details>

#### evaluates three-way comparison

- evaluates three-way comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates three-way comparison")
val a = 1
val b = 5
val c = 10
expect a < b and b < c
```

</details>

#### evaluates mixed comparison operators

- evaluates mixed comparison operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates mixed comparison operators")
val x = 5
expect 0 <= x and x <= 10
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
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

- Canonical SPipe generation for source `951b4969b057d7db67fdfeaf03c759e2f9f6b5742f26484e556bcc6c5d6b3736`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `951b4969b057d7db67fdfeaf03c759e2f9f6b5742f26484e556bcc6c5d6b3736`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `951b4969b057d7db67fdfeaf03c759e2f9f6b5742f26484e556bcc6c5d6b3736`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/array_types_spec.spl
mirror: doc/06_spec/03_system/feature/usage/array_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/array_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/array_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/array_types_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates array from literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/array_types_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets array length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/array_types_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets first and last elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Primitive Types Specification

> Tests for primitive types, type suffixes, union types, type aliases, and generic types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primitive Types Specification

Tests for primitive types, type suffixes, union types, type aliases, and generic types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PRIM-001 |
| Category | Language \| Types |
| Status | Implemented |
| Source | `test/feature/usage/primitive_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for primitive types, type suffixes, union types, type aliases,
and generic types.

## Syntax

```simple
use std.spec.step

val x = 42i32                             # Type suffix
type Number = i64                         # Type alias
fn process(x: i64 | str) -> i64: ...      # Union type
fn identity<T>(x: T) -> T: x              # Generic function
```

## Scenarios

### Enum Types

#### compares enum variants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compares enum variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("compares enum variants")
enum Color:
    Red
    Green
val c = Color.Green
var result = 0
if c == Color.Red:
    result = 1
else:
    result = 0
expect result == 0
```

</details>

### Union Types

#### accepts union type parameter

- accepts union type parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts union type parameter")
fn test(x: i64 | str) -> i64:
    return 42
expect test(10) == 42
```

</details>

### Type Aliases

#### uses simple type alias

- uses simple type alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses simple type alias")
type Number = i64
fn double(x: Number) -> Number:
    return x * 2
expect double(21) == 42
```

</details>

### Optional Types

#### accepts optional parameter

- accepts optional parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts optional parameter")
fn maybe_value(x: i64?) -> i64:
    return 5
expect maybe_value(10) == 5
```

</details>

### Generic Functions

#### defines identity function

- defines identity function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defines identity function")
fn identity<T>(x: T) -> T:
    return x
expect identity(42) == 42
```

</details>

#### uses two type parameters

- uses two type parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses two type parameters")
fn first<A, B>(a: A, b: B) -> A:
    return a
fn second<A, B>(a: A, b: B) -> B:
    return b
val x = first(10, 20)
val y = second(30, 40)
expect x + y == 50
```

</details>

### Generic Structs

#### creates generic struct

- creates generic struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates generic struct")
struct Box<T>:
    value: T
val b = Box { value: 42 }
expect b.value == 42
```

</details>

### Option Type Operations

#### unwraps Some value

- unwraps Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unwraps Some value")
val opt = Some(42)
expect opt.unwrap() == 42
```

</details>

#### unwraps None with default

- unwraps None with default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unwraps None with default")
val opt = None
expect opt.unwrap_or(99) == 99
```

</details>

#### checks is_some

- checks is_some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("checks is_some")
val opt = Some(1)
var result = 0
if opt.is_some():
    result = 1
expect result == 1
```

</details>

#### checks is_none

- checks is_none


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("checks is_none")
val opt = None
var result = 0
if opt.is_none():
    result = 1
expect result == 1
```

</details>

#### maps Some value

- maps Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maps Some value")
val opt = Some(10)
val res = opt.map(_1 * 2)
expect res.unwrap() == 20
```

</details>

### Type Suffixes

#### uses i32 suffix

- uses i32 suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses i32 suffix")
val x = 42i32
expect x == 42
```

</details>

#### uses i64 suffix

- uses i64 suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses i64 suffix")
val x = 100i64
expect x == 100
```

</details>

#### uses u32 suffix

- uses u32 suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses u32 suffix")
val x = 255u32
expect x == 255
```

</details>

#### uses unit suffix km

- uses unit suffix km


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses unit suffix km")
val distance = 100_km
expect distance.value() == 100
```

</details>

#### uses unit suffix in expression

- uses unit suffix in expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses unit suffix in expression")
val a = 50_m
val b = 30_m
expect (a + b).value() == 80
```

</details>

#### uses f64 suffix

- uses f64 suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses f64 suffix")
val x = 3.15f64
expect 1 == 1  # parsing test
```

</details>

#### uses f32 suffix

- uses f32 suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses f32 suffix")
val x = 1.5f32
expect 1 == 1  # parsing test
```

</details>

### Strong Enums

#### matches exhaustively without wildcard

- matches exhaustively without wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches exhaustively without wildcard")
@strong
enum Status:
    Active
    Inactive
    Pending
val s = Status.Active
var r = 0
match s:
    case Status.Active:
        r = 1
    case Status.Inactive:
        r = 2
    case Status.Pending:
        r = 3
expect r == 1
```

</details>

#### allows wildcard in weak enum

- allows wildcard in weak enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows wildcard in weak enum")
enum Status:
    Active
    Inactive
    Pending
val s = Status.Active
var result = 0
match s:
    case Status.Active:
        result = 1
    case _:
        result = 0
expect result == 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `62d7f0ea884e7764b136abc8b15730e4fc59034f3a67e86b0feb158871a33438`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62d7f0ea884e7764b136abc8b15730e4fc59034f3a67e86b0feb158871a33438`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62d7f0ea884e7764b136abc8b15730e4fc59034f3a67e86b0feb158871a33438`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/primitive_types_spec.spl
mirror: doc/06_spec/feature/usage/primitive_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/primitive_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/primitive_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/primitive_types_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares enum variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/primitive_types_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts union type parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/primitive_types_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses simple type alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

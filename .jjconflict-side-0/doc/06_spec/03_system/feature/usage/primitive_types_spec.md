# Primitive Types Specification

> Tests for primitive types, type suffixes, union types, type aliases, and generic types.

<!-- sdn-diagram:id=primitive_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=primitive_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

primitive_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=primitive_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/primitive_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for primitive types, type suffixes, union types, type aliases,
and generic types.

## Syntax

```simple
val x = 42i32                             # Type suffix
type Number = i64                         # Type alias
fn process(x: i64 | str) -> i64: ...      # Union type
fn identity<T>(x: T) -> T: x              # Generic function
```

## Scenarios

### Enum Types

#### compares enum variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn test
2. expect test


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test(x: i64 | str) -> i64:
    return 42
expect test(10) == 42
```

</details>

### Type Aliases

#### uses simple type alias

1. fn double
2. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Number = i64
fn double(x: Number) -> Number:
    return x * 2
expect double(21) == 42
```

</details>

### Optional Types

#### accepts optional parameter

1. fn maybe value
2. expect maybe value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn maybe_value(x: i64?) -> i64:
    return 5
expect maybe_value(10) == 5
```

</details>

### Generic Functions

#### defines identity function

1. fn identity<T>
2. expect identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    return x
expect identity(42) == 42
```

</details>

#### uses two type parameters

1. fn first<A, B>
2. fn second<A, B>


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Box<T>:
    value: T
val b = Box { value: 42 }
expect b.value == 42
```

</details>

### Option Type Operations

#### unwraps Some value

1. expect opt unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
expect opt.unwrap() == 42
```

</details>

#### unwraps None with default

1. expect opt unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = None
expect opt.unwrap_or(99) == 99
```

</details>

#### checks is_some

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(1)
var result = 0
if opt.is_some():
    result = 1
expect result == 1
```

</details>

#### checks is_none

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = None
var result = 0
if opt.is_none():
    result = 1
expect result == 1
```

</details>

#### maps Some value

1. expect res unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(10)
val res = opt.map(_1 * 2)
expect res.unwrap() == 20
```

</details>

### Type Suffixes

#### uses i32 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42i32
expect x == 42
```

</details>

#### uses i64 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100i64
expect x == 100
```

</details>

#### uses u32 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 255u32
expect x == 255
```

</details>

#### uses unit suffix km

1. expect distance value


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val distance = 100_km
expect distance.value() == 100
```

</details>

#### uses unit suffix in expression

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 50_m
val b = 30_m
expect (a + b).value() == 80
```

</details>

#### uses f64 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.15f64
expect 1 == 1  # parsing test
```

</details>

#### uses f32 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.5f32
expect 1 == 1  # parsing test
```

</details>

### Strong Enums

#### matches exhaustively without wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

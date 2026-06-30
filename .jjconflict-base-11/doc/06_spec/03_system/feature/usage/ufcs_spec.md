# UFCS (Uniform Function Call Syntax) Specification

> UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax. When `x.method()` is called, the compiler resolves in priority order: 1. Instance method on x's type (highest priority) 2. Trait method implemented by x's type 3. Free function `method(x)` where first param matches x's type (UFCS)

<!-- sdn-diagram:id=ufcs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ufcs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ufcs_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ufcs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UFCS (Uniform Function Call Syntax) Specification

UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax. When `x.method()` is called, the compiler resolves in priority order: 1. Instance method on x's type (highest priority) 2. Trait method implemented by x's type 3. Free function `method(x)` where first param matches x's type (UFCS)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3100-3120 |
| Category | Syntax |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/ufcs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax.
When `x.method()` is called, the compiler resolves in priority order:
1. Instance method on x's type (highest priority)
2. Trait method implemented by x's type
3. Free function `method(x)` where first param matches x's type (UFCS)

This enables fluent API chaining without requiring methods to be defined on types.

## Syntax

```simple
# Free function
fn double(x: i64) -> i64:
x * 2

# Usage via UFCS
val n = 5
val result = n.double()    # Resolves to: double(n)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| UFCS | Uniform Function Call Syntax - call free functions as methods |
| Resolution Priority | Instance > Trait > FreeFunction |
| Type Matching | First parameter type must be compatible with receiver |

## Implementation Notes

Files involved:
- `simple/compiler/hir.spl` - MethodResolution enum
- `simple/compiler/resolve.spl` - Resolution pass
- `simple/compiler/mir.spl` - Codegen support
- `simple/compiler/driver.spl` - Pipeline integration

## Scenarios

### UFCS Basic Functionality

#### with integer values

#### calls math.abs via dot notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = -5
val result = n.abs()
expect result == 5
```

</details>

#### calls math.sqrt via dot notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 16.0
val result = x.sqrt()
expect result == 4.0
```

</details>

#### with array values

#### calls array.len via dot notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
val result = arr.len()
expect result == 5
```

</details>

#### calls array.first via dot notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 30]
val result = arr.first()
expect result == 10
```

</details>

#### calls array.last via dot notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 30]
val result = arr.last()
expect result == 30
```

</details>

### UFCS Method Chaining

#### chaining multiple UFCS calls

#### chains abs and to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = -42
val result = n.abs().to_string()
expect result == "42"
```

</details>

#### chains array operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val result = arr.len().to_string()
expect result == "3"
```

</details>

### UFCS Priority Ordering

#### instance method takes priority

#### calls string.len method not free function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val result = s.len()
expect result == 5
```

</details>

#### calls array.push method

1. arr = arr push
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr = arr.push(4)
expect arr.len() == 4
```

</details>

### UFCS Type Matching

#### exact type matching

#### matches i64 receiver with i64 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64 = -5
val result = n.abs()
expect result == 5
```

</details>

#### matches f64 receiver with f64 parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: f64 = 16.0
val result = x.sqrt()
expect result == 4.0
```

</details>

### UFCS Edge Cases

#### with zero and negative values

#### works with zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 0
val result = n.abs()
expect result == 0
```

</details>

#### works with negative float

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -3.14
val result = x.abs()
expect result == 3.14
```

</details>

#### with empty collections

#### len of empty array is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
val result = arr.len()
expect result == 0
```

</details>

#### first of empty array is None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
val result = arr.first()
expect result == nil
```

</details>

#### receiver as expression

#### works with literal receiver

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-5).abs()
expect result == 5
```

</details>

#### works with arithmetic expression receiver

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (3 - 8).abs()
expect result == 5
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

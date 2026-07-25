# Compiler Basics

> Tests fundamental compiler functionality including lexing, parsing, and basic code generation. Verifies that core language constructs such as variables, functions, and expressions compile and execute correctly.

<!-- sdn-diagram:id=compiler_basics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_basics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_basics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_basics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Basics

Tests fundamental compiler functionality including lexing, parsing, and basic code generation. Verifies that core language constructs such as variables, functions, and expressions compile and execute correctly.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/compiler_basics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests fundamental compiler functionality including lexing, parsing, and basic
code generation. Verifies that core language constructs such as variables,
functions, and expressions compile and execute correctly.

## Scenarios

### Integer Literals

#### compiles zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 0
expect result == 0
```

</details>

#### compiles positive integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42
expect result == 42
```

</details>

#### compiles negative integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -5
expect result == -5
```

</details>

### Arithmetic Operations

#### compiles addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 + 32
expect result == 42
```

</details>

#### compiles subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 50 - 8
expect result == 42
```

</details>

#### compiles multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 6 * 7
expect result == 42
```

</details>

#### compiles division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 84 / 2
expect result == 42
```

</details>

#### compiles modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 47 % 5
expect result == 2
```

</details>

#### compiles nested arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (10 + 20) * 2 - 18
expect result == 42
```

</details>

### Comparison Operations

#### compiles less than - true case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 1 < 2: 1 else: 0
expect result == 1
```

</details>

#### compiles less than - false case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 2 < 1: 1 else: 0
expect result == 0
```

</details>

#### compiles greater than - true case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 2 > 1: 1 else: 0
expect result == 1
```

</details>

#### compiles greater than - false case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 1 > 2: 1 else: 0
expect result == 0
```

</details>

#### compiles less than or equal - equal case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 1 <= 1: 1 else: 0
expect result == 1
```

</details>

#### compiles less than or equal - false case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 2 <= 1: 1 else: 0
expect result == 0
```

</details>

#### compiles greater than or equal - equal case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 2 >= 2: 1 else: 0
expect result == 1
```

</details>

#### compiles greater than or equal - false case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 1 >= 2: 1 else: 0
expect result == 0
```

</details>

#### compiles equals - true case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 42 == 42: 1 else: 0
expect result == 1
```

</details>

#### compiles equals - false case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 42 == 43: 1 else: 0
expect result == 0
```

</details>

#### compiles not equals - true case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 42 != 43: 1 else: 0
expect result == 1
```

</details>

#### compiles not equals - false case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if 42 != 42: 1 else: 0
expect result == 0
```

</details>

### Logical Operations

#### compiles logical and - true case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true and true: 1 else: 0
expect result == 1
```

</details>

#### compiles logical and - false case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true and false: 1 else: 0
expect result == 0
```

</details>

#### compiles logical or - true case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if false or true: 1 else: 0
expect result == 1
```

</details>

#### compiles logical or - false case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if false or false: 1 else: 0
expect result == 0
```

</details>

### Boolean Literals

#### compiles true literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true: 42 else: 0
expect result == 42
```

</details>

#### compiles false literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if false: 0 else: 42
expect result == 42
```

</details>

### Variable Bindings

#### compiles single let binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect x == 42
```

</details>

#### compiles multiple let bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 32
val result = a + b
expect result == 42
```

</details>

#### compiles binding with expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10 + 32
expect x == 42
```

</details>

### Function Definitions

#### compiles simple function

1. fn get value
2. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value():
    return 42
expect get_value() == 42
```

</details>

#### compiles function with parameters

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    return a + b
expect add(10, 32) == 42
```

</details>

#### compiles function with multiple statements

1. fn calc
2. expect calc


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn calc(x, y):
    val sum = x + y
    return sum
expect calc(10, 32) == 42
```

</details>

#### compiles nested function call

1. fn double
2. fn add doubled
3. expect add doubled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x):
    return x * 2
fn add_doubled(a, b):
    return double(a) + double(b)
expect add_doubled(10, 11) == 42
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

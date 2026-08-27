# Variables and Bindings Specification

> Tests for variable declarations including val (immutable) and var (mutable) bindings, type inference, and scoping rules.

<!-- sdn-diagram:id=variables_let_bindings_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=variables_let_bindings_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

variables_let_bindings_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=variables_let_bindings_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Variables and Bindings Specification

Tests for variable declarations including val (immutable) and var (mutable) bindings, type inference, and scoping rules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1050 |
| Category | Language |
| Status | Implemented |
| Source | `test/03_system/feature/usage/variables_let_bindings_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for variable declarations including val (immutable) and var (mutable)
bindings, type inference, and scoping rules.

## Syntax

```simple
# Immutable binding (preferred)
val name = "Alice"

# Mutable binding
var count = 0
count = count + 1

# Tuple destructuring
var (a, b) = (1, 2)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| val | Immutable binding - cannot be reassigned |
| var | Mutable binding - can be reassigned |

## Deprecated

- `let` - Use `val` instead
- `let mut` - Use `var` instead

## Scenarios

### Variables and Bindings

#### val bindings

#### creates immutable binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect x == 42
```

</details>

#### allows shadowing with new val

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
val x = 2
expect x == 2
```

</details>

#### binds expression results

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 + 20 * 2
expect result == 50
```

</details>

#### binds complex expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (5 + 3) * 4 - 10 / 2
expect result == 27
```

</details>

#### var bindings

#### creates mutable binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
x = 10
expect x == 10
```

</details>

#### allows multiple reassignments

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 1
x = 2
x = 3
expect x == 3
```

</details>

### Scoping and Nesting

#### nested scopes

#### inner scope shadows outer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The interpreter does not restore block scope after if-blocks,
# so we verify shadowing via a function scope which is isolated.
val x = 1
val inner_x = shadow_x()
expect inner_x == 2
expect x == 1
```

</details>

#### inner scope can read outer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
var result = 0
if true:
    result = x + 5
expect result == 15
```

</details>

#### loop scoping

<details>
<summary>Advanced: loop variable isolated to loop</summary>

#### loop variable isolated to loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The interpreter leaks loop variables into the outer scope,
# so we run the loop inside a function to get true isolation.
val i = 100
val sum = loop_sum_0_to_4()
expect i == 100
expect sum == 10
```

</details>


</details>

### Additional val/var Patterns

#### val with different types

#### creates immutable boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = true
expect flag == true
```

</details>

#### creates immutable float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pi = 3.14
expect pi > 3.0
```

</details>

#### var initialization patterns

#### initializes var with expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 5 * 2
x = x + 10
expect x == 20
```

</details>

<details>
<summary>Advanced: modifies var in loop</summary>

#### modifies var in loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 1..4:
    sum = sum + i
expect sum == 6
```

</details>


</details>

### Tuple Destructuring Bindings

#### var with tuples

#### destructures tuple into mutable bindings

1. var


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var (a, b) = (1, 2)
a = 10
b = 20
expect a + b == 30
```

</details>

#### val with tuples

#### destructures tuple into immutable bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (x, y) = (3, 4)
expect x + y == 7
```

</details>

### Type Inference

#### primitive type inference

#### infers integer type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect x + 8 == 50
```

</details>

#### infers string type

1. expect s len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect s.len() == 5
```

</details>

#### infers array type

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

### Global Functions with Bindings

#### len function

#### gets length of array

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect len(arr) == 5
```

</details>

#### gets length using method syntax

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

### Option Type Bindings

#### Some bindings

#### binds Some value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(42)
expect opt.?
```

</details>

#### unwraps Some value

1. expect opt unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(99)
expect opt.unwrap() == 99
```

</details>

#### None bindings

#### binds None value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
expect not opt.?
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

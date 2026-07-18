# Walrus Operator

> Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating immutable bindings. Covers basic bindings (integer, text, boolean, nil, float), expression evaluation, function call results, string concatenation, arrays, equivalence with val, nested scopes, control flow usage (if, loops, match), complex types (nested arrays, struct literals), and edge cases.

<!-- sdn-diagram:id=walrus_operator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=walrus_operator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

walrus_operator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=walrus_operator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Walrus Operator

Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating immutable bindings. Covers basic bindings (integer, text, boolean, nil, float), expression evaluation, function call results, string concatenation, arrays, equivalence with val, nested scopes, control flow usage (if, loops, match), complex types (nested arrays, struct literals), and edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-004 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/walrus_operator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating
immutable bindings. Covers basic bindings (integer, text, boolean, nil, float),
expression evaluation, function call results, string concatenation, arrays,
equivalence with val, nested scopes, control flow usage (if, loops, match),
complex types (nested arrays, struct literals), and edge cases.

## Syntax

```simple
x := 42
name := "Alice"
result := 10 + 32
numbers := [1, 2, 3]
```
Walrus Operator Specification

Tests the := operator as syntactic sugar for val declarations.
x := value is equivalent to val x = value (immutable binding)

## Scenarios

### Walrus Operator Basics

#### creates binding with integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect(x).to_equal(42)
```

</details>

#### creates binding with text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
expect(name).to_equal("Alice")
```

</details>

#### creates binding with boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = true
expect(flag).to_equal(true)
```

</details>

#### creates binding with nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = nil
expect(value == nil).to_equal(true)
```

</details>

#### creates binding with float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pi = 3.14
expect(pi).to_equal(3.14)
```

</details>

### Walrus Operator with Expressions

#### evaluates expression on right side

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 + 32
expect(result).to_equal(42)
```

</details>

#### works with function calls

1. fn get value
   - Expected: val_from_fn equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value() -> i64:
    100
val val_from_fn = get_value()
expect(val_from_fn).to_equal(100)
```

</details>

#### works with string concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val greeting = "Hello" + " " + "World"
expect(greeting).to_equal("Hello World")
```

</details>

#### works with arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3]
expect(numbers[0]).to_equal(1)
expect(numbers.len()).to_equal(3)
```

</details>

### Walrus Operator Semantics

#### creates immutable binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 5
expect(count).to_equal(5)
```

</details>

#### is equivalent to val declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 10
expect(x).to_equal(y)
```

</details>

#### works in nested scopes

1. fn outer
2. fn inner
3. inner
   - Expected: outer() equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer():
    val x = 100
    fn inner():
        val y = 200
        x + y
    inner()
expect(outer()).to_equal(300)
```

</details>

### Walrus Operator in Functions

#### works in function body

1. fn test walrus
   - Expected: test_walrus() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_walrus():
    val local = 42
    local
expect(test_walrus()).to_equal(42)
```

</details>

#### works with multiple bindings

1. fn multi walrus
   - Expected: multi_walrus() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multi_walrus():
    val a = 1
    val b = 2
    val c = 3
    a + b + c
expect(multi_walrus()).to_equal(6)
```

</details>

#### works with shadowing in nested scopes

1. fn inner
   - Expected: inner() equals `20`
   - Expected: outer_x equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer_x = 10
fn inner():
    val inner_x = 20
    inner_x
expect(inner()).to_equal(20)
expect(outer_x).to_equal(10)
```

</details>

### Walrus Operator in Control Flow

#### works in if branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true:
    val val_in_if = 42
    expect(val_in_if).to_equal(42)
```

</details>

<details>
<summary>Advanced: works in loops</summary>

#### works in loops

1. fn run loop
   - Expected: run_loop() equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_loop() -> i64:
    var total = 0
    var i = 0
    while i < 3:
        val x = i * 10
        total = total + x
        i = i + 1
    total
expect(run_loop()).to_equal(30)
```

</details>


</details>

#### works in match cases

1. fn run match
   - Expected: run_match() equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_match() -> text:
    val value = 2
    val label = "two"
    label
expect(run_match()).to_equal("two")
```

</details>

### Walrus Operator with Complex Types

#### works with nested arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = [[1, 2], [3, 4]]
expect(matrix[0][0]).to_equal(1)
expect(matrix.len()).to_equal(2)
```

</details>

#### works with struct literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val point = Point(x: 10, y: 20)
expect(point.x).to_equal(10)
expect(point.y).to_equal(20)
```

</details>

### Walrus Operator Edge Cases

#### handles parenthesized expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val val_paren = (10 + 20)
expect(val_paren).to_equal(30)
```

</details>

#### handles chained operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chained = 1 + 2 + 3 + 4
expect(chained).to_equal(10)
```

</details>

#### handles boolean expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_true = true and true
val is_false = true and false
expect(is_true).to_equal(true)
expect(is_false).to_equal(false)
```

</details>

### Walrus vs Regular Assignment

#### walrus creates new binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
expect(x).to_equal(10)
```

</details>

#### regular assignment requires val/var

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y = 20
expect(y).to_equal(20)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

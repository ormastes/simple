# Type System Integration Specification

> <details>

<!-- sdn-diagram:id=type_system_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_system_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_system_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_system_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type System Integration Specification

## Scenarios

### Type Inference in Variable Declarations

#### infers i64 from integer literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect(x).to_equal(42)
```

</details>

#### infers f64 from float literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pi = 3.14
expect(pi).to_equal(3.14)
```

</details>

#### infers text from string literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val greeting = "Hello"
expect(greeting).to_equal("Hello")
```

</details>

#### infers bool from boolean literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = true
expect(flag).to_equal(true)
```

</details>

#### infers type from binary operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = 10 + 20
expect(sum).to_equal(30)
```

</details>

#### infers bool from comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_greater = 5 > 3
expect(is_greater).to_equal(true)
```

</details>

#### infers bool from logical operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val both_true = true and true
expect(both_true).to_equal(true)
```

</details>

### Type Checking in Function Calls

#### validates correct parameter types

1. fn multiply
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multiply(a: i64, b: i64) -> i64:
    a * b
val result = multiply(6, 7)
expect(result).to_equal(42)
```

</details>

#### works with mixed parameter types

1. fn format number
2. str
   - Expected: result equals `100 units`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn format_number(num: i64, suffix: text) -> text:
    str(num) + suffix
val result = format_number(100, " units")
expect(result).to_equal("100 units")
```

</details>

#### handles bool parameters

1. fn negate
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn negate(x: bool) -> bool:
    not x
val result = negate(false)
expect(result).to_equal(true)
```

</details>

#### handles f64 parameters

1. fn square
   - Expected: result equals `16.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x: f64) -> f64:
    x * x
val result = square(4.0)
expect(result).to_equal(16.0)
```

</details>

### Monomorphization Cache

#### caches function calls with same types

1. fn identity
   - Expected: result1 equals `10`
   - Expected: result2 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x):
    x
val result1 = identity(10)
val result2 = identity(20)
expect(result1).to_equal(10)
expect(result2).to_equal(20)
```

</details>

#### handles different type instantiations

1. fn first
   - Expected: int_result equals `42`
   - Expected: text_result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn first(a, b):
    a
val int_result = first(42, 100)
val text_result = first("hello", "world")
expect(int_result).to_equal(42)
expect(text_result).to_equal("hello")
```

</details>

### Complex Type System Features

#### combines type inference with type checking

1. fn process
   - Expected: output equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn process(value: i64) -> i64:
    value * 2
val input = 21
val output = process(input)
expect(output).to_equal(42)
```

</details>

#### works with nested function calls

1. fn add ten
2. fn double it
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add_ten(x: i64) -> i64:
    x + 10
fn double_it(y: i64) -> i64:
    y * 2
val result = double_it(add_ten(5))
expect(result).to_equal(30)
```

</details>

#### handles array types

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4, 5]
var sum: i64 = 0
for n in numbers:
    sum = sum + n
expect(sum).to_equal(15)
```

</details>

#### infers types in control flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val condition = 10 > 5
val message = if condition: "yes" else: "no"
expect(message).to_equal("yes")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/type_system_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Type Inference in Variable Declarations
- Type Checking in Function Calls
- Monomorphization Cache
- Complex Type System Features

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Arithmetic Operations Specification

> Arithmetic operations provide basic mathematical computations on numeric types. Simple supports integer and floating-point arithmetic with standard operators and correct operator precedence.

<!-- sdn-diagram:id=arithmetic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arithmetic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arithmetic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arithmetic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 83 | 83 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arithmetic Operations Specification

Arithmetic operations provide basic mathematical computations on numeric types. Simple supports integer and floating-point arithmetic with standard operators and correct operator precedence.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ARITH-001 to #ARITH-030 |
| Category | Language \| Operators |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/arithmetic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Arithmetic operations provide basic mathematical computations on numeric types.
Simple supports integer and floating-point arithmetic with standard operators
and correct operator precedence.

## Syntax

```simple
# Basic binary operators
2 + 3              # Addition
10 - 3             # Subtraction
4 * 5              # Multiplication
15 / 3             # Division
17 % 5             # Modulo (remainder)
2 ** 3             # Exponentiation (power)

# Unary operators
-x                 # Negation
+x                 # Positive (identity)

# Operator precedence (high to low)
# 1. Exponentiation (**)
# 2. Unary (-, +)
# 3. Multiplication, Division, Modulo (*, /, %)
# 4. Addition, Subtraction (+, -)
```

## Key Concepts

| Operator | Name | Operands | Result |
|----------|------|----------|--------|
| `+` | Addition | i64, f64 | Same type |
| `-` | Subtraction | i64, f64 | Same type |
| `*` | Multiplication | i64, f64 | Same type |
| `/` | Division | i64, f64 | Same type |
| `%` | Modulo | i64 | i64 |
| `**` | Power | i64, f64 | Same type |

## Behavior

- Integer division truncates toward zero
- Modulo has the sign of the dividend
- Type coercion follows standard rules
- Overflow behavior (wrapping, panic, or saturation) depends on context
- Division by zero is an error

## Scenarios

### Basic Binary Operators

#### addition

#### adds positive integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3 == 5
```

</details>

#### adds zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 + 0 == 5
expect 0 + 5 == 5
```

</details>

#### adds larger numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 100 + 200 == 300
```

</details>

#### adds negative integers

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ((-5)) + 3 == -2
```

</details>

#### subtraction

#### subtracts integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 - 3 == 7
```

</details>

#### subtracts zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 - 0 == 5
```

</details>

#### subtracts from zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 0 - 5 == -5
```

</details>

#### subtracts resulting in negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 3 - 10 == -7
```

</details>

#### multiplication

#### multiplies integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 4 * 5 == 20
```

</details>

#### multiplies by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 * 0 == 0
expect 0 * 5 == 0
```

</details>

#### multiplies by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 * 1 == 5
```

</details>

#### multiplies negative numbers

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ((-4)) * 5 == -20
expect ((-4)) * -5 == 20
```

</details>

#### division

#### divides integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 15 / 3 == 5
```

</details>

#### divides with truncation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 7 / 2 == 3
```

</details>

#### divides by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 / 1 == 42
```

</details>

#### divides zero by number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 0 / 5 == 0
```

</details>

#### divides negative numbers

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ((-20)) / 4 == -5
expect 20 / -4 == -5
```

</details>

### Operator Precedence

#### evaluates multiplication before addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3 * 4 == 14
```

</details>

#### evaluates multiplication before subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 - 3 * 2 == 4
```

</details>

#### evaluates division before addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 + 20 / 4 == 15
```

</details>

#### handles chain of same precedence (left-to-right)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 20 - 5 - 3 == 12
expect 20 / 4 / 2 == 2
```

</details>

#### respects multiple operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3 * 4 - 1 == 13
```

</details>

#### handles complex expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 * 3 + 4 * 5 == 26
```

</details>

### Parentheses and Expression Grouping

#### changes addition before multiplication

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 + 3) * 4 == 20
```

</details>

#### changes subtraction before division

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (20 - 4) / 2 == 8
```

</details>

#### handles nested parentheses

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ((2 + 3) * 4) + 1 == 21
```

</details>

#### handles deeply nested parentheses

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (((10 + 5) * 2) - 5) / 3 == 6
```

</details>

### Modulo Operation

#### calculates simple modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 17 % 5 == 2
```

</details>

#### modulo of exact division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 20 % 5 == 0
```

</details>

#### modulo with smaller divisor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 3 % 7 == 3
```

</details>

#### modulo with one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 % 1 == 0
```

</details>

#### modulo with negative dividend

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ((-17)) % 5 == -2
```

</details>

#### modulo with negative divisor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 17 % -5 == 2
```

</details>

### Unary Operators

#### negates positive number

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ((-5)) == -5
```

</details>

#### negates negative number

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (-(-5)) == 5
```

</details>

#### applies unary plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: unary plus not supported in parser
expect true
```

</details>

#### applies unary plus to negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: unary plus not supported in parser
expect true
```

</details>

#### negates in expression

1. expect 10 +


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 + (-5) == 5
```

</details>

### Floating Point Arithmetic

#### float addition

#### adds floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2.5 + 3.5 == 6.0
```

</details>

#### adds float and integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2.5 + 3 == 5.5
```

</details>

#### float subtraction

#### subtracts floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10.5 - 3.2 == 7.3
```

</details>

#### float multiplication

#### multiplies floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2.5 * 4.0 == 10.0
```

</details>

#### float division

#### divides floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10.0 / 2.0 == 5.0
```

</details>

#### divides with fractional result

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5.0 / 2.0 == 2.5
```

</details>

### Exponentiation

#### calculates 2 to power 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 ** 3 == 8
```

</details>

#### calculates any number to power 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 ** 0 == 1
```

</details>

#### calculates any number to power 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 ** 1 == 5
```

</details>

#### calculates 10 squared

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 ** 2 == 100
```

</details>

#### has higher precedence than multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 * 3 ** 2 == 18
```

</details>

### Mixed Type Arithmetic

#### adds integer to float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 + 2.5 == 7.5
```

</details>

#### multiplies integer by float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 4 * 2.5 == 10.0
```

</details>

#### divides integer by float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 / 2.5 == 4.0
```

</details>

#### complex mixed expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3.5 * 4 == 16.0
```

</details>

### Zero and Identity Cases

#### adds zero identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 + 0 == 42
```

</details>

#### multiplies by one identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 * 1 == 42
```

</details>

#### multiplies by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 * 0 == 0
```

</details>

#### subtracts zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 - 0 == 42
```

</details>

#### divides by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 / 1 == 42
```

</details>

### Negative Number Arithmetic

#### adds two negatives

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ((-5)) + -3 == -8
```

</details>

#### adds positive and negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 + -3 == 2
```

</details>

#### multiplies negatives

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ((-5)) * -3 == 15
```

</details>

#### multiplies positive and negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 * -3 == -15
```

</details>

#### divides negatives

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ((-20)) / -4 == 5
```

</details>

#### divides positive by negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 20 / -4 == -5
```

</details>

### Large Number Arithmetic

#### adds large numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1000000 + 2000000 == 3000000
```

</details>

#### multiplies large numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 100000 * 100 == 10000000
```

</details>

#### handles near max i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Not testing max itself to avoid overflow complexity
val big = 9000000000000000000
expect big + 0 == big
```

</details>

### Assignment with Arithmetic

#### uses arithmetic in variable assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 + 3 * 4
expect result == 14
```

</details>

#### chains multiple arithmetic operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val c = a + b * 2
expect c == 50
```

</details>

#### modifies variable with arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 10
x = x + 5
expect x == 15
```

</details>

#### multiple arithmetic assignments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
total = total + 5
total = total + 10
total = total + 3
expect total == 18
```

</details>

### Arithmetic in Collections

<details>
<summary>Advanced: sums array with loop</summary>

#### sums array with loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
var sum = 0
for i in arr:
    sum = sum + i
expect sum == 15
```

</details>


</details>

#### multiply each element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
var product = 1
for i in arr:
    product = product * i
expect product == 6
```

</details>

#### arithmetic on array indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[2 + 1] == 40
```

</details>

### Arithmetic in Conditionals

#### condition with addition

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (if 2 + 3 == 5: true else: false) == true
```

</details>

#### condition with multiplication

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (if 4 * 5 == 20: true else: false) == true
```

</details>

#### nested arithmetic in condition

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (if 2 * 3 + 4 == 10: true else: false) == true
```

</details>

#### arithmetic comparison

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (if 10 / 2 > 3: true else: false) == true
```

</details>

### Arithmetic Practical Examples

#### calculates average

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = 10 + 20 + 30
val avg = sum / 3
expect avg == 20
```

</details>

#### calculates compound interest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val principal = 1000
val rate = 5
val years = 2
val interest = principal * rate / 100 * years
expect interest == 100
```

</details>

#### calculates area of rectangle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val width = 10
val height = 5
val area = width * height
expect area == 50
```

</details>

#### converts between units

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kilometers = 5
val meters = kilometers * 1000
expect meters == 5000
```

</details>

#### calculates percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 200
val part = 50
val percent = part * 100 / total
expect percent == 25
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 83 |
| Active scenarios | 83 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

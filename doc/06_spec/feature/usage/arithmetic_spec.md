# Arithmetic Operations Specification

> Arithmetic operations provide basic mathematical computations on numeric types. Simple supports integer and floating-point arithmetic with standard operators and correct operator precedence.

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
| Source | `test/feature/usage/arithmetic_spec.spl` |
| Updated | 2026-08-26 |
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

- adds positive integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds positive integers")
expect 2 + 3 == 5
```

</details>

#### adds zero

- adds zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds zero")
expect 5 + 0 == 5
expect 0 + 5 == 5
```

</details>

#### adds larger numbers

- adds larger numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds larger numbers")
expect 100 + 200 == 300
```

</details>

#### adds negative integers

- adds negative integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds negative integers")
expect ((-5)) + 3 == -2
```

</details>

#### subtraction

#### subtracts integers

- subtracts integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts integers")
expect 10 - 3 == 7
```

</details>

#### subtracts zero

- subtracts zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts zero")
expect 5 - 0 == 5
```

</details>

#### subtracts from zero

- subtracts from zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts from zero")
expect 0 - 5 == -5
```

</details>

#### subtracts resulting in negative

- subtracts resulting in negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts resulting in negative")
expect 3 - 10 == -7
```

</details>

#### multiplication

#### multiplies integers

- multiplies integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies integers")
expect 4 * 5 == 20
```

</details>

#### multiplies by zero

- multiplies by zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies by zero")
expect 5 * 0 == 0
expect 0 * 5 == 0
```

</details>

#### multiplies by one

- multiplies by one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies by one")
expect 5 * 1 == 5
```

</details>

#### multiplies negative numbers

- multiplies negative numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies negative numbers")
expect ((-4)) * 5 == -20
expect ((-4)) * -5 == 20
```

</details>

#### division

#### divides integers

- divides integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides integers")
expect 15 / 3 == 5
```

</details>

#### divides with truncation

- divides with truncation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides with truncation")
expect 7 / 2 == 3
```

</details>

#### divides by one

- divides by one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides by one")
expect 42 / 1 == 42
```

</details>

#### divides zero by number

- divides zero by number


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides zero by number")
expect 0 / 5 == 0
```

</details>

#### divides negative numbers

- divides negative numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides negative numbers")
expect ((-20)) / 4 == -5
expect 20 / -4 == -5
```

</details>

### Operator Precedence

#### evaluates multiplication before addition

- evaluates multiplication before addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates multiplication before addition")
expect 2 + 3 * 4 == 14
```

</details>

#### evaluates multiplication before subtraction

- evaluates multiplication before subtraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates multiplication before subtraction")
expect 10 - 3 * 2 == 4
```

</details>

#### evaluates division before addition

- evaluates division before addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates division before addition")
expect 10 + 20 / 4 == 15
```

</details>

#### handles chain of same precedence (left-to-right)

- handles chain of same precedence (left-to-right)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles chain of same precedence (left-to-right)")
expect 20 - 5 - 3 == 12
expect 20 / 4 / 2 == 2
```

</details>

#### respects multiple operations

- respects multiple operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("respects multiple operations")
expect 2 + 3 * 4 - 1 == 13
```

</details>

#### handles complex expression

- handles complex expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles complex expression")
expect 2 * 3 + 4 * 5 == 26
```

</details>

### Parentheses and Expression Grouping

#### changes addition before multiplication

- changes addition before multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("changes addition before multiplication")
expect (2 + 3) * 4 == 20
```

</details>

#### changes subtraction before division

- changes subtraction before division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("changes subtraction before division")
expect (20 - 4) / 2 == 8
```

</details>

#### handles nested parentheses

- handles nested parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested parentheses")
expect ((2 + 3) * 4) + 1 == 21
```

</details>

#### handles deeply nested parentheses

- handles deeply nested parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles deeply nested parentheses")
expect (((10 + 5) * 2) - 5) / 3 == 6
```

</details>

### Modulo Operation

#### calculates simple modulo

- calculates simple modulo


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates simple modulo")
expect 17 % 5 == 2
```

</details>

#### modulo of exact division

- modulo of exact division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("modulo of exact division")
expect 20 % 5 == 0
```

</details>

#### modulo with smaller divisor

- modulo with smaller divisor


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("modulo with smaller divisor")
expect 3 % 7 == 3
```

</details>

#### modulo with one

- modulo with one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("modulo with one")
expect 5 % 1 == 0
```

</details>

#### modulo with negative dividend

- modulo with negative dividend


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("modulo with negative dividend")
expect ((-17)) % 5 == -2
```

</details>

#### modulo with negative divisor

- modulo with negative divisor


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("modulo with negative divisor")
expect 17 % -5 == 2
```

</details>

### Unary Operators

#### negates positive number

- negates positive number


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negates positive number")
expect ((-5)) == -5
```

</details>

#### negates negative number

- negates negative number


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negates negative number")
expect (-(-5)) == 5
```

</details>

#### applies unary plus

- applies unary plus


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("applies unary plus")
# Skipped: unary plus not supported in parser
expect true
```

</details>

#### applies unary plus to negative

- applies unary plus to negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("applies unary plus to negative")
# Skipped: unary plus not supported in parser
expect true
```

</details>

#### negates in expression

- negates in expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negates in expression")
expect 10 + (-5) == 5
```

</details>

### Floating Point Arithmetic

#### float addition

#### adds floats

- adds floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds floats")
expect 2.5 + 3.5 == 6.0
```

</details>

#### adds float and integer

- adds float and integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds float and integer")
expect 2.5 + 3 == 5.5
```

</details>

#### float subtraction

#### subtracts floats

- subtracts floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts floats")
expect 10.5 - 3.2 == 7.3
```

</details>

#### float multiplication

#### multiplies floats

- multiplies floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies floats")
expect 2.5 * 4.0 == 10.0
```

</details>

#### float division

#### divides floats

- divides floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides floats")
expect 10.0 / 2.0 == 5.0
```

</details>

#### divides with fractional result

- divides with fractional result


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides with fractional result")
expect 5.0 / 2.0 == 2.5
```

</details>

### Exponentiation

#### calculates 2 to power 3

- calculates 2 to power 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates 2 to power 3")
expect 2 ** 3 == 8
```

</details>

#### calculates any number to power 0

- calculates any number to power 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates any number to power 0")
expect 5 ** 0 == 1
```

</details>

#### calculates any number to power 1

- calculates any number to power 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates any number to power 1")
expect 5 ** 1 == 5
```

</details>

#### calculates 10 squared

- calculates 10 squared


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates 10 squared")
expect 10 ** 2 == 100
```

</details>

#### has higher precedence than multiplication

- has higher precedence than multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has higher precedence than multiplication")
expect 2 * 3 ** 2 == 18
```

</details>

### Mixed Type Arithmetic

#### adds integer to float

- adds integer to float


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds integer to float")
expect 5 + 2.5 == 7.5
```

</details>

#### multiplies integer by float

- multiplies integer by float


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies integer by float")
expect 4 * 2.5 == 10.0
```

</details>

#### divides integer by float

- divides integer by float


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides integer by float")
expect 10 / 2.5 == 4.0
```

</details>

#### complex mixed expression

- complex mixed expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("complex mixed expression")
expect 2 + 3.5 * 4 == 16.0
```

</details>

### Zero and Identity Cases

#### adds zero identity

- adds zero identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds zero identity")
expect 42 + 0 == 42
```

</details>

#### multiplies by one identity

- multiplies by one identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies by one identity")
expect 42 * 1 == 42
```

</details>

#### multiplies by zero

- multiplies by zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies by zero")
expect 42 * 0 == 0
```

</details>

#### subtracts zero

- subtracts zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts zero")
expect 42 - 0 == 42
```

</details>

#### divides by one

- divides by one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides by one")
expect 42 / 1 == 42
```

</details>

### Negative Number Arithmetic

#### adds two negatives

- adds two negatives


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds two negatives")
expect ((-5)) + -3 == -8
```

</details>

#### adds positive and negative

- adds positive and negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds positive and negative")
expect 5 + -3 == 2
```

</details>

#### multiplies negatives

- multiplies negatives


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies negatives")
expect ((-5)) * -3 == 15
```

</details>

#### multiplies positive and negative

- multiplies positive and negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies positive and negative")
expect 5 * -3 == -15
```

</details>

#### divides negatives

- divides negatives


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides negatives")
expect ((-20)) / -4 == 5
```

</details>

#### divides positive by negative

- divides positive by negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides positive by negative")
expect 20 / -4 == -5
```

</details>

### Large Number Arithmetic

#### adds large numbers

- adds large numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds large numbers")
expect 1000000 + 2000000 == 3000000
```

</details>

#### multiplies large numbers

- multiplies large numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies large numbers")
expect 100000 * 100 == 10000000
```

</details>

#### handles near max i64

- handles near max i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles near max i64")
# Not testing max itself to avoid overflow complexity
val big = 9000000000000000000
expect big + 0 == big
```

</details>

### Assignment with Arithmetic

#### uses arithmetic in variable assignment

- uses arithmetic in variable assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses arithmetic in variable assignment")
val result = 2 + 3 * 4
expect result == 14
```

</details>

#### chains multiple arithmetic operations

- chains multiple arithmetic operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains multiple arithmetic operations")
val a = 10
val b = 20
val c = a + b * 2
expect c == 50
```

</details>

#### modifies variable with arithmetic

- modifies variable with arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("modifies variable with arithmetic")
var x = 10
x = x + 5
expect x == 15
```

</details>

#### multiple arithmetic assignments

- multiple arithmetic assignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple arithmetic assignments")
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

- sums array with loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sums array with loop")
val arr = [1, 2, 3, 4, 5]
var sum = 0
for i in arr:
    sum = sum + i
expect sum == 15
```

</details>


</details>

#### multiply each element

- multiply each element


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiply each element")
val arr = [1, 2, 3]
var product = 1
for i in arr:
    product = product * i
expect product == 6
```

</details>

#### arithmetic on array indices

- arithmetic on array indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("arithmetic on array indices")
val arr = [10, 20, 30, 40, 50]
expect arr[2 + 1] == 40
```

</details>

### Arithmetic in Conditionals

#### condition with addition

- condition with addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("condition with addition")
expect (if 2 + 3 == 5: true else: false) == true
```

</details>

#### condition with multiplication

- condition with multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("condition with multiplication")
expect (if 4 * 5 == 20: true else: false) == true
```

</details>

#### nested arithmetic in condition

- nested arithmetic in condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("nested arithmetic in condition")
expect (if 2 * 3 + 4 == 10: true else: false) == true
```

</details>

#### arithmetic comparison

- arithmetic comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("arithmetic comparison")
expect (if 10 / 2 > 3: true else: false) == true
```

</details>

### Arithmetic Practical Examples

#### calculates average

- calculates average


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates average")
val sum = 10 + 20 + 30
val avg = sum / 3
expect avg == 20
```

</details>

#### calculates compound interest

- calculates compound interest


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates compound interest")
val principal = 1000
val rate = 5
val years = 2
val interest = principal * rate / 100 * years
expect interest == 100
```

</details>

#### calculates area of rectangle

- calculates area of rectangle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates area of rectangle")
val width = 10
val height = 5
val area = width * height
expect area == 50
```

</details>

#### converts between units

- converts between units


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts between units")
val kilometers = 5
val meters = kilometers * 1000
expect meters == 5000
```

</details>

#### calculates percentage

- calculates percentage


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates percentage")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `779dd533307d9ed76aea96c89e1f89fb6a803543ec4a0194d67f4dfaa51da236`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `779dd533307d9ed76aea96c89e1f89fb6a803543ec4a0194d67f4dfaa51da236`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `779dd533307d9ed76aea96c89e1f89fb6a803543ec4a0194d67f4dfaa51da236`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/arithmetic_spec.spl
mirror: doc/06_spec/feature/usage/arithmetic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/arithmetic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/arithmetic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/arithmetic_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds positive integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/arithmetic_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/arithmetic_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds larger numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

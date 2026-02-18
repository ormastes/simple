# Arithmetic Operations Specification
*Source:* `test/feature/usage/arithmetic_spec.spl`
**Feature IDs:** #ARITH-001 to #ARITH-030  |  **Category:** Language | Operators  |  **Status:** Implemented

## Overview



use std.text.{NL}

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

## Feature: Basic Binary Operators

## Basic Binary Operators

    Tests for fundamental arithmetic operators on integers.

### Scenario: addition

| # | Example | Status |
|---|---------|--------|
| 1 | adds positive integers | pass |
| 2 | adds zero | pass |
| 3 | adds larger numbers | pass |
| 4 | adds negative integers | pass |

**Example:** adds positive integers
    Then  expect 2 + 3 == 5

**Example:** adds zero
    Then  expect 5 + 0 == 5
    Then  expect 0 + 5 == 5

**Example:** adds larger numbers
    Then  expect 100 + 200 == 300

**Example:** adds negative integers
    Then  expect ((-5)) + 3 == -2

### Scenario: subtraction

| # | Example | Status |
|---|---------|--------|
| 1 | subtracts integers | pass |
| 2 | subtracts zero | pass |
| 3 | subtracts from zero | pass |
| 4 | subtracts resulting in negative | pass |

**Example:** subtracts integers
    Then  expect 10 - 3 == 7

**Example:** subtracts zero
    Then  expect 5 - 0 == 5

**Example:** subtracts from zero
    Then  expect 0 - 5 == -5

**Example:** subtracts resulting in negative
    Then  expect 3 - 10 == -7

### Scenario: multiplication

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies integers | pass |
| 2 | multiplies by zero | pass |
| 3 | multiplies by one | pass |
| 4 | multiplies negative numbers | pass |

**Example:** multiplies integers
    Then  expect 4 * 5 == 20

**Example:** multiplies by zero
    Then  expect 5 * 0 == 0
    Then  expect 0 * 5 == 0

**Example:** multiplies by one
    Then  expect 5 * 1 == 5

**Example:** multiplies negative numbers
    Then  expect ((-4)) * 5 == -20
    Then  expect ((-4)) * -5 == 20

### Scenario: division

| # | Example | Status |
|---|---------|--------|
| 1 | divides integers | pass |
| 2 | divides with truncation | pass |
| 3 | divides by one | pass |
| 4 | divides zero by number | pass |
| 5 | divides negative numbers | pass |

**Example:** divides integers
    Then  expect 15 / 3 == 5

**Example:** divides with truncation
    Then  expect 7 / 2 == 3

**Example:** divides by one
    Then  expect 42 / 1 == 42

**Example:** divides zero by number
    Then  expect 0 / 5 == 0

**Example:** divides negative numbers
    Then  expect ((-20)) / 4 == -5
    Then  expect 20 / -4 == -5

## Feature: Operator Precedence

## Operator Precedence

    Tests that operators are evaluated in the correct order.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates multiplication before addition | pass |
| 2 | evaluates multiplication before subtraction | pass |
| 3 | evaluates division before addition | pass |
| 4 | handles chain of same precedence (left-to-right) | pass |
| 5 | respects multiple operations | pass |
| 6 | handles complex expression | pass |

**Example:** evaluates multiplication before addition
    Then  expect 2 + 3 * 4 == 14

**Example:** evaluates multiplication before subtraction
    Then  expect 10 - 3 * 2 == 4

**Example:** evaluates division before addition
    Then  expect 10 + 20 / 4 == 15

**Example:** handles chain of same precedence (left-to-right)
    Then  expect 20 - 5 - 3 == 12
    Then  expect 20 / 4 / 2 == 2

**Example:** respects multiple operations
    Then  expect 2 + 3 * 4 - 1 == 13

**Example:** handles complex expression
    Then  expect 2 * 3 + 4 * 5 == 26

## Feature: Parentheses and Expression Grouping

## Parentheses and Expression Grouping

    Tests that parentheses override default precedence.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | changes addition before multiplication | pass |
| 2 | changes subtraction before division | pass |
| 3 | handles nested parentheses | pass |
| 4 | handles deeply nested parentheses | pass |

**Example:** changes addition before multiplication
    Then  expect (2 + 3) * 4 == 20

**Example:** changes subtraction before division
    Then  expect (20 - 4) / 2 == 8

**Example:** handles nested parentheses
    Then  expect ((2 + 3) * 4) + 1 == 21

**Example:** handles deeply nested parentheses
    Then  expect (((10 + 5) * 2) - 5) / 3 == 6

## Feature: Modulo Operation

## Modulo Operation

    Tests remainder calculation via modulo operator.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calculates simple modulo | pass |
| 2 | modulo of exact division | pass |
| 3 | modulo with smaller divisor | pass |
| 4 | modulo with one | pass |
| 5 | modulo with negative dividend | pass |
| 6 | modulo with negative divisor | pass |

**Example:** calculates simple modulo
    Then  expect 17 % 5 == 2

**Example:** modulo of exact division
    Then  expect 20 % 5 == 0

**Example:** modulo with smaller divisor
    Then  expect 3 % 7 == 3

**Example:** modulo with one
    Then  expect 5 % 1 == 0

**Example:** modulo with negative dividend
    Then  expect ((-17)) % 5 == -2

**Example:** modulo with negative divisor
    Then  expect 17 % -5 == 2

## Feature: Unary Operators

## Unary Operators

    Tests unary negation and positive operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | negates positive number | pass |
| 2 | negates negative number | pass |
| 3 | applies unary plus | pass |
| 4 | applies unary plus to negative | pass |
| 5 | negates in expression | pass |

**Example:** negates positive number
    Then  expect ((-5)) == -5

**Example:** negates negative number
    Then  expect (-(-5)) == 5

**Example:** applies unary plus
    Then  expect true

**Example:** applies unary plus to negative
    Then  expect true

**Example:** negates in expression
    Then  expect 10 + (-5) == 5

## Feature: Floating Point Arithmetic

## Floating Point Arithmetic

    Tests arithmetic operations on floating-point numbers.

### Scenario: float addition

| # | Example | Status |
|---|---------|--------|
| 1 | adds floats | pass |
| 2 | adds float and integer | pass |

**Example:** adds floats
    Then  expect 2.5 + 3.5 == 6.0

**Example:** adds float and integer
    Then  expect 2.5 + 3 == 5.5

### Scenario: float subtraction

| # | Example | Status |
|---|---------|--------|
| 1 | subtracts floats | pass |

**Example:** subtracts floats
    Then  expect 10.5 - 3.2 == 7.3

### Scenario: float multiplication

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies floats | pass |

**Example:** multiplies floats
    Then  expect 2.5 * 4.0 == 10.0

### Scenario: float division

| # | Example | Status |
|---|---------|--------|
| 1 | divides floats | pass |
| 2 | divides with fractional result | pass |

**Example:** divides floats
    Then  expect 10.0 / 2.0 == 5.0

**Example:** divides with fractional result
    Then  expect 5.0 / 2.0 == 2.5

## Feature: Exponentiation

## Exponentiation

    Tests power/exponentiation operator.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calculates 2 to power 3 | pass |
| 2 | calculates any number to power 0 | pass |
| 3 | calculates any number to power 1 | pass |
| 4 | calculates 10 squared | pass |
| 5 | has higher precedence than multiplication | pass |

**Example:** calculates 2 to power 3
    Then  expect 2 ** 3 == 8

**Example:** calculates any number to power 0
    Then  expect 5 ** 0 == 1

**Example:** calculates any number to power 1
    Then  expect 5 ** 1 == 5

**Example:** calculates 10 squared
    Then  expect 10 ** 2 == 100

**Example:** has higher precedence than multiplication
    Then  expect 2 * 3 ** 2 == 18

## Feature: Mixed Type Arithmetic

## Mixed Type Arithmetic

    Tests arithmetic between integers and floats.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | adds integer to float | pass |
| 2 | multiplies integer by float | pass |
| 3 | divides integer by float | pass |
| 4 | complex mixed expression | pass |

**Example:** adds integer to float
    Then  expect 5 + 2.5 == 7.5

**Example:** multiplies integer by float
    Then  expect 4 * 2.5 == 10.0

**Example:** divides integer by float
    Then  expect 10 / 2.5 == 4.0

**Example:** complex mixed expression
    Then  expect 2 + 3.5 * 4 == 16.0

## Feature: Zero and Identity Cases

## Zero and Identity Cases

    Tests edge cases with zero and identity elements.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | adds zero identity | pass |
| 2 | multiplies by one identity | pass |
| 3 | multiplies by zero | pass |
| 4 | subtracts zero | pass |
| 5 | divides by one | pass |

**Example:** adds zero identity
    Then  expect 42 + 0 == 42

**Example:** multiplies by one identity
    Then  expect 42 * 1 == 42

**Example:** multiplies by zero
    Then  expect 42 * 0 == 0

**Example:** subtracts zero
    Then  expect 42 - 0 == 42

**Example:** divides by one
    Then  expect 42 / 1 == 42

## Feature: Negative Number Arithmetic

## Negative Number Arithmetic

    Tests arithmetic with negative values.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | adds two negatives | pass |
| 2 | adds positive and negative | pass |
| 3 | multiplies negatives | pass |
| 4 | multiplies positive and negative | pass |
| 5 | divides negatives | pass |
| 6 | divides positive by negative | pass |

**Example:** adds two negatives
    Then  expect ((-5)) + -3 == -8

**Example:** adds positive and negative
    Then  expect 5 + -3 == 2

**Example:** multiplies negatives
    Then  expect ((-5)) * -3 == 15

**Example:** multiplies positive and negative
    Then  expect 5 * -3 == -15

**Example:** divides negatives
    Then  expect ((-20)) / -4 == 5

**Example:** divides positive by negative
    Then  expect 20 / -4 == -5

## Feature: Large Number Arithmetic

## Large Number Arithmetic

    Tests arithmetic with large values.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | adds large numbers | pass |
| 2 | multiplies large numbers | pass |
| 3 | handles near max i64 | pass |

**Example:** adds large numbers
    Then  expect 1000000 + 2000000 == 3000000

**Example:** multiplies large numbers
    Then  expect 100000 * 100 == 10000000

**Example:** handles near max i64
    Given val big = 9000000000000000000
    Then  expect big + 0 == big

## Feature: Assignment with Arithmetic

## Assignment with Arithmetic

    Tests combining arithmetic with variable assignment.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses arithmetic in variable assignment | pass |
| 2 | chains multiple arithmetic operations | pass |
| 3 | modifies variable with arithmetic | pass |
| 4 | multiple arithmetic assignments | pass |

**Example:** uses arithmetic in variable assignment
    Given val result = 2 + 3 * 4
    Then  expect result == 14

**Example:** chains multiple arithmetic operations
    Given val a = 10
    Given val b = 20
    Given val c = a + b * 2
    Then  expect c == 50

**Example:** modifies variable with arithmetic
    Given var x = 10
    Then  expect x == 15

**Example:** multiple arithmetic assignments
    Given var total = 0
    Then  expect total == 18

## Feature: Arithmetic in Collections

## Arithmetic in Collections

    Tests arithmetic operations when used with arrays and loops.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | sums array with loop | pass |
| 2 | multiply each element | pass |
| 3 | arithmetic on array indices | pass |

**Example:** sums array with loop
    Given val arr = [1, 2, 3, 4, 5]
    Given var sum = 0
    Then  expect sum == 15

**Example:** multiply each element
    Given val arr = [1, 2, 3]
    Given var product = 1
    Then  expect product == 6

**Example:** arithmetic on array indices
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[2 + 1] == 40

## Feature: Arithmetic in Conditionals

## Arithmetic in Conditionals

    Tests arithmetic expressions in if/else conditions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | condition with addition | pass |
| 2 | condition with multiplication | pass |
| 3 | nested arithmetic in condition | pass |
| 4 | arithmetic comparison | pass |

**Example:** condition with addition
    Then  expect (if 2 + 3 == 5: true else: false) == true

**Example:** condition with multiplication
    Then  expect (if 4 * 5 == 20: true else: false) == true

**Example:** nested arithmetic in condition
    Then  expect (if 2 * 3 + 4 == 10: true else: false) == true

**Example:** arithmetic comparison
    Then  expect (if 10 / 2 > 3: true else: false) == true

## Feature: Arithmetic Practical Examples

## Practical Examples

    Real-world arithmetic scenarios.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calculates average | pass |
| 2 | calculates compound interest | pass |
| 3 | calculates area of rectangle | pass |
| 4 | converts between units | pass |
| 5 | calculates percentage | pass |

**Example:** calculates average
    Given val sum = 10 + 20 + 30
    Given val avg = sum / 3
    Then  expect avg == 20

**Example:** calculates compound interest
    Given val principal = 1000
    Given val rate = 5
    Given val years = 2
    Given val interest = principal * rate / 100 * years
    Then  expect interest == 100

**Example:** calculates area of rectangle
    Given val width = 10
    Given val height = 5
    Given val area = width * height
    Then  expect area == 50

**Example:** converts between units
    Given val kilometers = 5
    Given val meters = kilometers * 1000
    Then  expect meters == 5000

**Example:** calculates percentage
    Given val total = 200
    Given val part = 50
    Given val percent = part * 100 / total
    Then  expect percent == 25



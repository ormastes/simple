# Arithmetic Operations Specification

**Feature ID:** #ARITH-001 to #ARITH-030 | **Category:** Language | Operators | **Difficulty:** 1/5 | **Status:** Implemented

_Source: `test/feature/usage/arithmetic_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 83 |

## Test Structure

### Basic Binary Operators

#### addition

- ✅ adds positive integers
- ✅ adds zero
- ✅ adds larger numbers
- ✅ adds negative integers
#### subtraction

- ✅ subtracts integers
- ✅ subtracts zero
- ✅ subtracts from zero
- ✅ subtracts resulting in negative
#### multiplication

- ✅ multiplies integers
- ✅ multiplies by zero
- ✅ multiplies by one
- ✅ multiplies negative numbers
#### division

- ✅ divides integers
- ✅ divides with truncation
- ✅ divides by one
- ✅ divides zero by number
- ✅ divides negative numbers
### Operator Precedence

- ✅ evaluates multiplication before addition
- ✅ evaluates multiplication before subtraction
- ✅ evaluates division before addition
- ✅ handles chain of same precedence (left-to-right)
- ✅ respects multiple operations
- ✅ handles complex expression
### Parentheses and Expression Grouping

- ✅ changes addition before multiplication
- ✅ changes subtraction before division
- ✅ handles nested parentheses
- ✅ handles deeply nested parentheses
### Modulo Operation

- ✅ calculates simple modulo
- ✅ modulo of exact division
- ✅ modulo with smaller divisor
- ✅ modulo with one
- ✅ modulo with negative dividend
- ✅ modulo with negative divisor
### Unary Operators

- ✅ negates positive number
- ✅ negates negative number
- ✅ applies unary plus
- ✅ applies unary plus to negative
- ✅ negates in expression
### Floating Point Arithmetic

#### float addition

- ✅ adds floats
- ✅ adds float and integer
#### float subtraction

- ✅ subtracts floats
#### float multiplication

- ✅ multiplies floats
#### float division

- ✅ divides floats
- ✅ divides with fractional result
### Exponentiation

- ✅ calculates 2 to power 3
- ✅ calculates any number to power 0
- ✅ calculates any number to power 1
- ✅ calculates 10 squared
- ✅ has higher precedence than multiplication
### Mixed Type Arithmetic

- ✅ adds integer to float
- ✅ multiplies integer by float
- ✅ divides integer by float
- ✅ complex mixed expression
### Zero and Identity Cases

- ✅ adds zero identity
- ✅ multiplies by one identity
- ✅ multiplies by zero
- ✅ subtracts zero
- ✅ divides by one
### Negative Number Arithmetic

- ✅ adds two negatives
- ✅ adds positive and negative
- ✅ multiplies negatives
- ✅ multiplies positive and negative
- ✅ divides negatives
- ✅ divides positive by negative
### Large Number Arithmetic

- ✅ adds large numbers
- ✅ multiplies large numbers
- ✅ handles near max i64
### Assignment with Arithmetic

- ✅ uses arithmetic in variable assignment
- ✅ chains multiple arithmetic operations
- ✅ modifies variable with arithmetic
- ✅ multiple arithmetic assignments
### Arithmetic in Collections

- ✅ sums array with loop
- ✅ multiply each element
- ✅ arithmetic on array indices
### Arithmetic in Conditionals

- ✅ condition with addition
- ✅ condition with multiplication
- ✅ nested arithmetic in condition
- ✅ arithmetic comparison
### Arithmetic Practical Examples

- ✅ calculates average
- ✅ calculates compound interest
- ✅ calculates area of rectangle
- ✅ converts between units
- ✅ calculates percentage


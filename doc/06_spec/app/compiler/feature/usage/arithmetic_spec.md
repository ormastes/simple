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
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 83 |
| Active scenarios | 83 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Arithmetic operations provide basic mathematical computations on numeric types.
Simple supports integer and floating-point arithmetic with standard operators
and correct operator precedence.

## Syntax

```simple
2 + 3              # Addition
10 - 3             # Subtraction
4 * 5              # Multiplication
15 / 3             # Division
17 % 5             # Modulo (remainder)
2 ** 3             # Exponentiation (power)

-x                 # Negation
+x                 # Positive (identity)

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/arithmetic/result.json` |

## Scenarios

- adds positive integers
- adds zero
- adds larger numbers
- adds negative integers
- subtracts integers
- subtracts zero
- subtracts from zero
- subtracts resulting in negative
- multiplies integers
- multiplies by zero
- multiplies by one
- multiplies negative numbers
- divides integers
- divides with truncation
- divides by one
- divides zero by number
- divides negative numbers
- evaluates multiplication before addition
- evaluates multiplication before subtraction
- evaluates division before addition
- handles chain of same precedence (left-to-right)
- respects multiple operations
- handles complex expression
- changes addition before multiplication
- changes subtraction before division
- handles nested parentheses
- handles deeply nested parentheses
- calculates simple modulo
- modulo of exact division
- modulo with smaller divisor
- modulo with one
- modulo with negative dividend
- modulo with negative divisor
- negates positive number
- negates negative number
- applies unary plus
- applies unary plus to negative
- negates in expression
- adds floats
- adds float and integer
- subtracts floats
- multiplies floats
- divides floats
- divides with fractional result
- calculates 2 to power 3
- calculates any number to power 0
- calculates any number to power 1
- calculates 10 squared
- has higher precedence than multiplication
- adds integer to float
- multiplies integer by float
- divides integer by float
- complex mixed expression
- adds zero identity
- multiplies by one identity
- multiplies by zero
- subtracts zero
- divides by one
- adds two negatives
- adds positive and negative
- multiplies negatives
- multiplies positive and negative
- divides negatives
- divides positive by negative
- adds large numbers
- multiplies large numbers
- handles near max i64
- uses arithmetic in variable assignment
- chains multiple arithmetic operations
- modifies variable with arithmetic
- multiple arithmetic assignments
- sums array with loop
- multiply each element
- arithmetic on array indices
- condition with addition
- condition with multiplication
- nested arithmetic in condition
- arithmetic comparison
- calculates average
- calculates compound interest
- calculates area of rectangle
- converts between units
- calculates percentage

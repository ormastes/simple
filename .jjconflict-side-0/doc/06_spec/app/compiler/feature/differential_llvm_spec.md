# LLVM Backend Differential Testing

**Feature ID:** #COMPILER-001 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/compiler/backend/differential_llvm_spec.spl`_

---

## Overview

Compares LLVM backend output with Cranelift and Interpreter backends to ensure all produce
identical results for identical inputs. Tests cover arithmetic operations (addition, subtraction,
multiplication, division, modulo, negation), bitwise operations (AND, OR, XOR, shifts, NOT),
comparison operators, control flow (if/else, for/while loops), function calls including recursion,
variable mutability, boolean logic, complex nested expressions, edge cases with zero and boundary
values, type conversions, aggregates (tuples), and string operations.

## Syntax

```simple
fn factorial(n: i64) -> i64:
    if n <= 1: 1
    else: n * factorial(n - 1)
val result = factorial(5)
expect(result).to_equal(120)

val result = (2 + 3) * (4 + 5)
expect(result).to_equal(45)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 56 |

## Test Structure

### Differential Testing - Arithmetic

#### integer addition

- ✅ computes 2 + 3 correctly
- ✅ computes large numbers
- ✅ handles negative numbers
#### integer subtraction

- ✅ computes 10 - 4 correctly
- ✅ handles negative results
#### integer multiplication

- ✅ computes 6 * 7 correctly
- ✅ handles zero
#### integer division

- ✅ computes 20 / 4 correctly
- ✅ truncates toward zero
#### modulo operation

- ✅ computes 10 % 3 correctly
#### negation

- ✅ negates positive number
- ✅ negates negative number
### Differential Testing - Bitwise

#### bitwise AND

- ✅ computes 12 & 10 correctly
#### bitwise OR

- ✅ computes 12 | 10 correctly
#### bitwise XOR

- ✅ computes 12 ^ 10 correctly
#### left shift

- ✅ computes 5 << 2 correctly
#### right shift

- ✅ computes 20 >> 2 correctly
#### bitwise NOT

- ✅ computes ~0 correctly
### Differential Testing - Comparisons

#### equality

- ✅ compares equal numbers
- ✅ compares unequal numbers
#### inequality

- ✅ compares different numbers
#### less than

- ✅ compares smaller to larger
- ✅ compares larger to smaller
#### less than or equal

- ✅ compares equal numbers
- ✅ compares smaller to larger
#### greater than

- ✅ compares larger to smaller
#### greater than or equal

- ✅ compares equal numbers
### Differential Testing - Control Flow

#### if statements

- ✅ executes then branch
- ✅ executes else branch
#### loops

- ✅ executes for loop
- ✅ executes while loop
### Differential Testing - Functions

#### simple functions

- ✅ calls function with no parameters
- ✅ calls function with parameters
- ✅ calls function multiple times
#### recursive functions

- ✅ computes factorial
### Differential Testing - Variables

#### immutable variables

- ✅ reads immutable variable
#### mutable variables

- ✅ updates mutable variable
- ✅ updates multiple times
### Differential Testing - Boolean Logic

#### logical AND

- ✅ computes true && true
- ✅ computes true && false
#### logical OR

- ✅ computes false || true
- ✅ computes false || false
#### logical NOT

- ✅ computes !true
- ✅ computes !false
### Differential Testing - Complex Expressions

#### nested arithmetic

- ✅ evaluates (2 + 3) * (4 + 5)
- ✅ respects operator precedence
#### mixed operations

- ✅ combines arithmetic and bitwise
- ✅ combines comparisons and logic
### Differential Testing - Edge Cases

#### zero values

- ✅ handles zero in addition
- ✅ handles zero in multiplication
#### boundary values

- ✅ handles small positive number
- ✅ handles negative numbers
### Differential Testing - Type Conversions

#### integer types

- ✅ works with i64
### Differential Testing - Aggregates

#### tuples

- ✅ creates and accesses tuple
### Differential Testing - Strings

#### string operations

- ✅ works with string literals
### Differential Testing - Summary

#### comprehensive smoke test

- ✅ runs comprehensive computation


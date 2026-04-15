# Math Block Tensor Operations Specification

**Feature ID:** #1090-1098 (subset: tensor ops) | **Category:** Syntax / Math DSL | **Difficulty:** 4/5 | **Status:** Implemented

_Source: `test/feature/usage/math_blocks_spec.spl`_

---

## Overview

The `m{}` math block supports torch-compatible tensor operations for numerical computing.
Each math block is a self-contained DSL expression that returns a Block value.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 28 |

## Test Structure

### Math Block Arithmetic

- ✅ evaluates addition
- ✅ evaluates subtraction
- ✅ evaluates multiplication
- ✅ evaluates division
- ✅ evaluates complex expression
- ✅ respects operator precedence
- ✅ evaluates power
- ✅ evaluates negative numbers
### Math Block Functions

- ✅ evaluates sqrt of 16
- ✅ evaluates sqrt of 9
- ✅ evaluates abs of negative
- ✅ evaluates abs of positive
- ✅ evaluates frac
- ✅ evaluates nested functions
### Math Block Matrix Operations

- ✅ computes dot product
- ✅ computes dot product simple
### Math Block Constants

- ✅ evaluates pi greater than 3
- ✅ evaluates pi less than 4
- ✅ evaluates e greater than 2
- ✅ evaluates e less than 3
### Math Block Array Expressions

- ✅ evaluates array subscript
- ✅ evaluates nested array subscript
### Math Block LaTeX Compatibility

- ✅ evaluates LaTeX frac
- ✅ evaluates LaTeX sqrt
- ✅ evaluates Greek letter pi
### Math Block LaTeX Export

- ✅ exports simple arithmetic
- ✅ exports fractions
- ✅ exports Greek letters


# Pipeline Multi Specification

**Feature ID:** #TBD | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/compiler/pipeline_multi_spec.spl`_

---

## Overview

Tests the full compilation pipeline with multiple program variants,
covering arithmetic, control flow, recursion, string output, arrays,
and mutable variables.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 51 |

## Test Structure

### Pipeline Multi - Return Values

- ✅ return 0
- ✅ return 42
- ✅ explicit return statement
- ✅ simple arithmetic
- ✅ nested arithmetic
- ✅ variable declaration
- ✅ if-else expression
- ✅ while loop
- ✅ multiple variables
- ✅ nested if-else
- ✅ factorial 5
- ✅ subtraction
- ✅ var decrement in while
- ✅ sum 1..5
- ✅ greater-than-or-equal operator
- ✅ equality operator
- ✅ inequality operator
### Pipeline Multi - Functions

- ✅ function call
- ✅ nested function calls
- ✅ recursion fibonacci(6)=8
- ✅ multiple functions
- ✅ division
- ✅ modulo
- ✅ deep recursion fibonacci(10)=55
- ✅ 3-argument function
- ✅ call chain
- ✅ GCD algorithm
- ✅ power of 2 via loop
- ✅ register pressure test
- ✅ 4-argument function
- ✅ spill across calls
- ✅ mutual recursion is_even(10)=1
- ✅ Collatz steps for 6
- ✅ 5-argument function
- ✅ nested while loops (3x4=12)
- ✅ boolean range check
- ✅ Ackermann(2,3)=9
### Pipeline Multi - String Output

- ✅ puts Hello
- ✅ multiple puts calls
- ✅ puts and return value
- ✅ printf with int arg
- ✅ printf with 2 int args
- ✅ puts then compute
### Pipeline Multi - Arrays

- ✅ array index [1]
- ✅ array index [0]+[2]
- ✅ array with computed index
### Pipeline Multi - Mutable Variables

- ✅ mutable variable reassignment
- ✅ multiple reassignments double
- ✅ compound variable operations
- ✅ malloc heap allocation
- ✅ array element sum via function


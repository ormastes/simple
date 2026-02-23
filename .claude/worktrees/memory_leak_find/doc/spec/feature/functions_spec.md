# Function Definitions Specification

**Feature ID:** #1004 | **Category:** Language | **Status:** In Progress

_Source: `test/feature/usage/functions_spec.spl`_

---

Tests for function definition and invocation.
Verifies function parameters, return types, implicit returns, and various calling patterns.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 19 |

## Test Structure

### Function Definitions

#### basic function definition

- ✅ defines function with explicit return type
- ✅ uses implicit return of last expression
- ✅ calls function with no parameters
#### function parameters

- ✅ passes multiple parameters
- ✅ uses type inference for parameters
- ✅ uses named arguments
#### function return types

- ✅ returns single value
- ✅ returns early with explicit return
- ✅ returns without explicit type annotation
#### function with no return

- ✅ executes function with side effects
- ✅ calls function multiple times
#### higher-order functions

- ✅ accepts function parameter
- ✅ uses lambda function
- ✅ returns function
#### generic functions

- ✅ defines generic function
- ✅ uses generic with constraints
- ✅ uses multiple type parameters
#### recursive functions

- ✅ defines recursive factorial function
- ✅ uses tail recursion


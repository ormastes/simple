# Compiler Basics Specification

**Feature ID:** #COMPILER-BASICS-001 | **Category:** Compiler | Core | **Status:** Implemented

_Source: `test/feature/compiler/compiler_basics_spec.spl`_

---

## Overview

Tests for core compiler functionality - verifies that code compiles and executes
correctly through the compiler pipeline (HIR → MIR → execution).

## Syntax

```simple
# Integer literals
val x = 42

# Arithmetic operations
val sum = 10 + 32
val diff = 50 - 8

# Comparison operations
val is_less = 1 < 2

# Logical operations
val both = true and false
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Integer Literal | Compile-time integer constant |
| Arithmetic | Binary arithmetic operations (+, -, *, /, %) |
| Comparison | Binary comparison operations (<, >, <=, >=, ==, !=) |
| Logical | Boolean operations (and, or, not) |
| Let Binding | Variable binding (val/let) |
| Function | Function definition and call |

## Behavior

- Integer literals compile to immediate values
- Arithmetic operations follow standard precedence
- Comparisons return boolean values
- Logical operations short-circuit

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 34 |

## Test Structure

### Integer Literals

- ✅ compiles zero
- ✅ compiles positive integer
- ✅ compiles negative integer
### Arithmetic Operations

- ✅ compiles addition
- ✅ compiles subtraction
- ✅ compiles multiplication
- ✅ compiles division
- ✅ compiles modulo
- ✅ compiles nested arithmetic
### Comparison Operations

- ✅ compiles less than - true case
- ✅ compiles less than - false case
- ✅ compiles greater than - true case
- ✅ compiles greater than - false case
- ✅ compiles less than or equal - equal case
- ✅ compiles less than or equal - false case
- ✅ compiles greater than or equal - equal case
- ✅ compiles greater than or equal - false case
- ✅ compiles equals - true case
- ✅ compiles equals - false case
- ✅ compiles not equals - true case
- ✅ compiles not equals - false case
### Logical Operations

- ✅ compiles logical and - true case
- ✅ compiles logical and - false case
- ✅ compiles logical or - true case
- ✅ compiles logical or - false case
### Boolean Literals

- ✅ compiles true literal
- ✅ compiles false literal
### Variable Bindings

- ✅ compiles single let binding
- ✅ compiles multiple let bindings
- ✅ compiles binding with expression
### Function Definitions

- ✅ compiles simple function
- ✅ compiles function with parameters
- ✅ compiles function with multiple statements
- ✅ compiles nested function call


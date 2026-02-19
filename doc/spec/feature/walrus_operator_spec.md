# Walrus Operator

**Feature ID:** #SYNTAX-004 | **Category:** Syntax | **Status:** Active

_Source: `test/feature/usage/walrus_operator_spec.spl`_

---

## Overview

Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating
immutable bindings. Covers basic bindings (integer, text, boolean, nil, float),
expression evaluation, function call results, string concatenation, arrays,
equivalence with val, nested scopes, control flow usage (if, loops, match),
complex types (nested arrays, struct literals), and edge cases.

## Syntax

```simple
x := 42
name := "Alice"
result := 10 + 32
numbers := [1, 2, 3]
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 25 |

## Test Structure

### Walrus Operator Basics

- ✅ creates binding with integer
- ✅ creates binding with text
- ✅ creates binding with boolean
- ✅ creates binding with nil
- ✅ creates binding with float
### Walrus Operator with Expressions

- ✅ evaluates expression on right side
- ✅ works with function calls
- ✅ works with string concatenation
- ✅ works with arrays
### Walrus Operator Semantics

- ✅ creates immutable binding
- ✅ is equivalent to val declaration
- ✅ works in nested scopes
### Walrus Operator in Functions

- ✅ works in function body
- ✅ works with multiple bindings
- ✅ works with shadowing in nested scopes
### Walrus Operator in Control Flow

- ✅ works in if branches
- ✅ works in loops
- ✅ works in match cases
### Walrus Operator with Complex Types

- ✅ works with nested arrays
- ✅ works with struct literals
### Walrus Operator Edge Cases

- ✅ handles parenthesized expressions
- ✅ handles chained operations
- ✅ handles boolean expressions
### Walrus vs Regular Assignment

- ✅ walrus creates new binding
- ✅ regular assignment requires val/var


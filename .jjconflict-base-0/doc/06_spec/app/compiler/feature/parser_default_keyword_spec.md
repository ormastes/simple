# Default Parameter Values

**Feature ID:** #PARSER-001 | **Category:** Syntax | **Status:** Active

_Source: `test/feature/usage/parser_default_keyword_spec.spl`_

---

## Overview

Tests the `default` keyword for function parameter default values using `=`
syntax. Covers basic defaults, typed parameters, methods (instance and static),
collection defaults, edge cases (booleans, negatives, expressions), and
combinations of required and default parameters across functions, classes,
and nested scopes.

## Syntax

```simple
fn greet(name = "World"):
    return "Hello, {name}"
fn typed_default(count: i32 = 0):
    return count
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 18 |

## Test Structure

### Default keyword in function parameters

- ✅ parses default parameter value with = syntax
- ✅ parses multiple default parameters
- ✅ overrides single default parameter
- ✅ parses default with expressions
- ✅ parses default with arithmetic
- ✅ uses default in nested function
### Default keyword with types

- ✅ parses default parameter with type annotation
- ✅ parses default text parameter
- ✅ parses default float parameter
### Default keyword in methods

- ✅ parses default in class method
- ✅ parses default in static method
### Default keyword with collections

- ✅ parses default empty array
- ✅ parses default array literal
### Default keyword edge cases

- ✅ parses default with boolean
- ✅ parses default with negative number
- ✅ parses default with string interpolation
### Default keyword combinations

- ✅ parses mix of required and default parameters
- ✅ parses multiple functions with defaults


# Default Arguments Specification

**Feature ID:** #DEFARG-001 | **Category:** Language | Functions | **Status:** Implemented

_Source: `test/feature/usage/default_arguments_spec.spl`_

---

## Overview

Tests for function default argument values.

## Syntax

```simple
fn greet(name, greeting="Hello"):
    print "{greeting}, {name}!"

greet("Alice")           # Uses default: "Hello, Alice!"
greet("Bob", "Hi")       # Override: "Hi, Bob!"
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 4 |

## Test Structure

### Default Arguments

- ✅ uses default argument when not provided
- ✅ overrides default argument when provided
- ✅ uses multiple default arguments
- ✅ overrides some default arguments


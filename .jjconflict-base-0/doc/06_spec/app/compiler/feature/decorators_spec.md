# Decorators Specification

**Feature ID:** #DECO-001 | **Category:** Language | Functions | **Status:** Implemented

_Source: `test/feature/usage/decorators_spec.spl`_

---

## Overview

Decorators are functions that transform other functions, enabling
aspect-oriented programming patterns like logging, caching, and validation.

## Syntax

```simple
# Basic decorator
@double_result
fn add_one(x):
    return x + 1

# Decorator with arguments
@multiply_by(3)
fn increment(x):
    return x + 1
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### Decorators

- ✅ applies basic decorator
- ✅ applies decorator with arguments
- ✅ stacks multiple decorators
- ✅ uses decorator without parentheses
### Attributes

- ✅ uses inline attribute
- ✅ uses deprecated attribute
- ✅ uses deprecated with message
- ✅ stacks multiple attributes
### Context Managers

- ✅ executes basic with block
- ✅ binds value with as clause


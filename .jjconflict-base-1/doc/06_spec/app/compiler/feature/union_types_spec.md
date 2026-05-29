# Union Type Declarations and Discrimination

**Feature ID:** #LANG-034 | **Category:** Language | **Status:** Planned

_Source: `test/feature/usage/union_types_spec.spl`_

---

## Overview

Union types allow a variable to hold a value of one of several specified types,
written as `A | B`. At runtime the language provides type discrimination so that
pattern matching or type-checking can narrow a union back to a concrete type.
This spec is a placeholder that will be expanded once the union type feature
lands; the planned coverage includes declaring union type annotations, assigning
values of different member types, and narrowing via `match` with type-case arms.

## Syntax

```simple
# Planned union type declaration (not yet implemented)
val value: Int | Str = 42

# Planned pattern-match narrowing
match value:
    case Int(n): print("number: {n}")
    case Str(s): print("string: {s}")
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Union type (`A \| B`) | A type that can hold a value belonging to any of its member types |
| Type discrimination | Runtime mechanism to determine which member type a union value actually is |
| Pattern narrowing | Using `match` with type-case arms to safely extract the concrete value |
| Planned status | Feature is not yet implemented; spec contains a placeholder test only |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### Union Types

- ✅ placeholder test


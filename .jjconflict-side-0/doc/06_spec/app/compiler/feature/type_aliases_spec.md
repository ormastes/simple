# Type Aliases Specification

**Feature ID:** #TYPE-ALIAS-001 to #TYPE-ALIAS-012 | **Category:** Language | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/type_aliases_spec.spl`_

---

## Overview

Type aliases allow creating alternative names for existing types, improving
code readability and maintainability. They enable domain-specific naming
without introducing new types, and support generic type aliases for
parameterized type shortcuts.

## Syntax

```simple
type UserId = i64
type IntList = [i64]
type StringMap = {str: str}
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Alias | Alternative name for an existing type |
| Collection Alias | Alias for array or dict types |
| Alias Chain | Alias that references another alias |

## Behavior

- Type aliases are fully interchangeable with their target type
- Aliases can reference collection types
- Aliases do not create new types (unlike newtypes)
- Aliases can reference other aliases (chaining)

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Type Aliases

#### with simple aliases

- ✅ aliases primitive types
- ✅ allows alias in function signature
- ✅ is interchangeable with base type
#### with collection aliases

- ✅ aliases array types
- ✅ aliases dict types
- ✅ allows nested collection aliases
#### with alias chains

- ✅ supports alias of alias
- ✅ supports multiple levels of aliasing
### Type Alias Usage

#### in struct fields

- ✅ uses alias in struct definition
#### in class fields

- ✅ uses alias in class definition
#### with return types

- ✅ uses alias as return type


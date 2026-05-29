# Primitive Types Specification

**Feature ID:** #PRIM-001 | **Category:** Language | Types | **Status:** Implemented

_Source: `test/feature/usage/primitive_types_spec.spl`_

---

## Overview

Tests for primitive types, type suffixes, union types, type aliases,
and generic types.

## Syntax

```simple
val x = 42i32                             # Type suffix
type Number = i64                         # Type alias
fn process(x: i64 | str) -> i64: ...      # Union type
fn identity<T>(x: T) -> T: x              # Generic function
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 21 |

## Test Structure

### Enum Types

- ✅ compares enum variants
### Union Types

- ✅ accepts union type parameter
### Type Aliases

- ✅ uses simple type alias
### Optional Types

- ✅ accepts optional parameter
### Generic Functions

- ✅ defines identity function
- ✅ uses two type parameters
### Generic Structs

- ✅ creates generic struct
### Option Type Operations

- ✅ unwraps Some value
- ✅ unwraps None with default
- ✅ checks is_some
- ✅ checks is_none
- ✅ maps Some value
### Type Suffixes

- ✅ uses i32 suffix
- ✅ uses i64 suffix
- ✅ uses u32 suffix
- ✅ uses unit suffix km
- ✅ uses unit suffix in expression
- ✅ uses f64 suffix
- ✅ uses f32 suffix
### Strong Enums

- ✅ matches exhaustively without wildcard
- ✅ allows wildcard in weak enum


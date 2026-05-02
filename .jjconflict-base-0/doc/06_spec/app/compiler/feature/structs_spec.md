# Structs Specification

**Feature ID:** #TBD | **Category:** Language | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/structs_spec.spl`_

---

## Overview

Structs are user-defined data types that group related fields together.
They support named fields with type annotations, default values, and can
have methods defined via impl blocks. Structs are the primary way to
define custom data structures in Simple.

## Syntax

```simple
struct Point:
    x: i64
    y: i64

struct Config:
    host: String = "localhost"
    port: i64 = 8080

val p = Point { x: 3, y: 4 }
val c = Config { port: 9000 }  # host uses default
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Struct | User-defined data type with named fields |
| Field | Named member of a struct with type annotation |
| Default Value | Optional value used when field not provided |
| Construction | Creating struct instance with field values |

## Behavior

- Fields are accessed using dot notation: `point.x`
- Construction requires all fields without defaults
- Fields can have default values
- Structs are value types (copied by default)

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### Structs

#### struct definition and construction

- ✅ defines struct with fields
- ✅ constructs struct with all fields
#### struct field access

- ✅ accesses struct fields
### Impl Blocks

- ✅ adds method to struct
- ✅ adds method with arguments
### Classes

- ✅ defines class with static method
### Context Blocks

- ✅ dispatches methods to context object
- ✅ accesses self fields in context
### Method Missing

- ✅ calls method_missing for unknown method
- ✅ passes arguments to method_missing


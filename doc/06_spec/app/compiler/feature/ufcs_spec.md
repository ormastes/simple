# UFCS (Uniform Function Call Syntax) Specification

**Feature ID:** #3100-3120 | **Category:** Syntax | **Difficulty:** 4/5 | **Status:** Implemented

_Source: `test/feature/usage/ufcs_spec.spl`_

---

## Overview

UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax.
When `x.method()` is called, the compiler resolves in priority order:
1. Instance method on x's type (highest priority)
2. Trait method implemented by x's type
3. Free function `method(x)` where first param matches x's type (UFCS)

This enables fluent API chaining without requiring methods to be defined on types.

## Syntax

```simple
# Free function
fn double(x: i64) -> i64:
    x * 2

# Usage via UFCS
val n = 5
val result = n.double()    # Resolves to: double(n)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| UFCS | Uniform Function Call Syntax - call free functions as methods |
| Resolution Priority | Instance > Trait > FreeFunction |
| Type Matching | First parameter type must be compatible with receiver |

## Implementation Notes

Files involved:
- `simple/compiler/hir.spl` - MethodResolution enum
- `simple/compiler/resolve.spl` - Resolution pass
- `simple/compiler/mir.spl` - Codegen support
- `simple/compiler/driver.spl` - Pipeline integration

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 17 |

## Test Structure

### UFCS Basic Functionality

#### with integer values

- ✅ calls math.abs via dot notation
- ✅ calls math.sqrt via dot notation
#### with array values

- ✅ calls array.len via dot notation
- ✅ calls array.first via dot notation
- ✅ calls array.last via dot notation
### UFCS Method Chaining

#### chaining multiple UFCS calls

- ✅ chains abs and to_string
- ✅ chains array operations
### UFCS Priority Ordering

#### instance method takes priority

- ✅ calls string.len method not free function
- ✅ calls array.push method
### UFCS Type Matching

#### exact type matching

- ✅ matches i64 receiver with i64 parameter
- ✅ matches f64 receiver with f64 parameter
### UFCS Edge Cases

#### with zero and negative values

- ✅ works with zero
- ✅ works with negative float
#### with empty collections

- ✅ len of empty array is zero
- ✅ first of empty array is None
#### receiver as expression

- ✅ works with literal receiver
- ✅ works with arithmetic expression receiver


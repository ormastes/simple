# Static Method Resolution

**Feature ID:** #RESOLVE-001 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/usage/static_method_resolution_spec.spl`_

---

## Overview

Tests static method resolution and calling in interpreter mode, verifying HIR/MIR
changes work correctly. Covers basic static method calls with and without
parameters, static vs instance method distinction, static method chaining with
instance methods, static-to-static calls, struct static methods, and error
cases for non-existent or misidentified static methods.

## Syntax

```simple
class Point:
    x: i64
    y: i64
    static fn origin() -> Point:
        Point(x: 0, y: 0)
val p = Point__origin()
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 13 |

## Test Structure

### Static Method Resolution

#### Basic static method resolution

- ✅ resolves simple static method call
- ✅ resolves static method with parameters
- ✅ resolves static method returning object
#### Static vs instance method distinction

- ✅ correctly resolves static method vs instance method
- ✅ allows same name for static and instance methods
#### Static method chaining

- ✅ chains static method call with instance method
- ✅ calls multiple static methods in sequence
#### Static methods calling other methods

- ✅ static method calls another static method
- ✅ static method creates object and calls instance method
#### Static method in structs

- ✅ resolves static method on struct
- ✅ resolves multiple static methods on struct
#### Error cases

- ✅ reports error for non-existent static method
- ✅ reports error for calling instance method as static


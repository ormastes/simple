# Classes and Object-Oriented Programming Specification

**Feature ID:** #OOP-001 | **Category:** Language | Classes | **Status:** Implemented

_Source: `test/feature/usage/classes_spec.spl`_

---

## Overview

Tests for class definitions, instance creation, field access, methods,
impl blocks, context blocks, method_missing, auto-forwarding properties,
and static polymorphism with interface bindings.

## Syntax

```simple
class Calculator:
    static fn add(a, b):
        return a + b

struct Point:
    x: i64
    y: i64

impl Point:
    fn sum(self):
        return self.x + self.y

context obj:
    method()  # Dispatches to obj.method()
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 23 |

## Test Structure

### Static Class Methods

- ✅ calls static method on class
- ✅ calls multiple static methods
### Impl Blocks

- ✅ adds method to struct via impl
- ✅ adds method with arguments via impl
### Class Instantiation

- ✅ creates instances with direct construction
- ✅ accesses string field
- ✅ creates class with default field values
### Instance Methods

- ✅ calls instance method
- ✅ calls method with arguments
### Context Blocks

- ✅ dispatches method to context object
- ✅ accesses self fields in context method
### Method Missing

- ✅ calls method_missing for unknown method
- ✅ passes arguments to method_missing
- ✅ uses method_missing in context block
### Auto-Forwarding Properties

- ✅ gets property via get_ method
- ✅ sets property via set_ method returning new instance
- ✅ checks boolean property via is_ method
- ✅ uses combined getter and setter
### Static Polymorphism

- ✅ binds trait to concrete class
- ✅ binds trait with multiple methods
- ✅ binds trait with fields
- ✅ passes bound trait as function parameter
### Trait Polymorphism

- ✅ calculates different areas via Shape trait


# Traits Specification

**Feature ID:** #TBD | **Category:** Language | **Difficulty:** 3/5 | **Status:** Implemented

_Source: `test/feature/usage/traits_spec.spl`_

---

## Overview

Traits define shared behavior that types can implement, enabling polymorphism
and code reuse. They are similar to interfaces in other languages but support
default implementations, associated types, and trait bounds for generics.

## Syntax

```simple
trait Printable:
    fn print(self)

trait Addable:
    fn add(self, other: Self) -> Self

    fn double(self) -> Self:  # Default implementation
        self.add(self)

impl Printable for Point:
    fn print(self):
        print("({x}, {y})")
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Trait | Interface defining shared behavior |
| Implementation | Concrete behavior for a specific type |
| Default Method | Trait method with provided implementation |
| Trait Bound | Generic constraint requiring trait implementation |

## Behavior

- Traits define method signatures types must implement
- Default methods provide optional implementations
- Types can implement multiple traits
- Trait bounds constrain generic type parameters

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 17 |

## Test Structure

### Traits

#### basic trait implementation

- ✅ implements trait for struct
- ✅ implements trait with arguments
#### multiple trait implementations

- ✅ allows multiple types to implement same trait
#### multiple traits on one type

- ✅ type implements two different traits
- ✅ type implements three traits
### Default Trait Methods

- ✅ uses default trait method when not overridden
- ✅ allows overriding default trait method
- ✅ default method can call abstract method
- ✅ default method can call other default method
### Dynamic Trait Objects

- ✅ coerces concrete type to dyn Trait via let binding
- ✅ passes concrete type to dyn Trait parameter
- ✅ handles multiple types via dyn Trait
- ✅ dyn Trait with default method
### Trait and Mixin Integration

- ✅ trait impl accesses mixin fields
- ✅ multiple traits on class with mixin
- ✅ dyn Trait dispatch on mixin class
- ✅ mixin method and trait method coexist


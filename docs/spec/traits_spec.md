# Traits

*Source: `simple/std_lib/test/features/language/traits_spec.spl`*

---

# Traits

**Feature ID:** #31
**Category:** Language
**Difficulty:** Level 4/5
**Status:** Complete
**Implementation:** Rust

## Overview

Trait definitions for shared behavior. Supports impl Trait for Type, default methods,
dynamic dispatch with dyn Trait, and TraitObject coercion.

## Syntax

```simple
trait TraitName:
    fn required_method() -> Type
    fn default_method() -> Type:
        return default_value

impl TraitName for StructName:
    fn required_method() -> Type:
        return implementation

# Dynamic dispatch
val obj: dyn Trait = concrete_value
fn process(x: dyn Trait) -> Type
```

## Implementation

**Files:**
- src/compiler/src/interpreter.rs - Trait evaluation
- src/compiler/src/interpreter_method.rs - Method dispatch
- src/parser/src/statements/mod.rs - Trait parsing

**Tests:**
- src/driver/tests/interpreter_oop.rs

**Dependencies:** Features #1, #2, #11, #14
**Required By:** Feature #32

## Notes

Traits enable polymorphism. dyn Trait creates TraitObjects for runtime dispatch.

# Feature #31: Traits

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #31 |
| **Feature Name** | Traits |
| **Category** | Language |
| **Difficulty** | 4 (Hard) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Trait definitions for shared behavior. Supports impl Trait for Type, default methods, dynamic dispatch with dyn Trait, and TraitObject coercion.

## Specification

[doc/spec/traits.md](../../spec/traits.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/parser/src/statements/mod.rs` | Trait parsing |
| `src/compiler/src/hir/types.rs` | Trait implementation |

## Syntax

```simple
trait TraitName:
    fn required_method(self) -> Type

    fn default_method(self) -> Type:
        return default_value

impl TraitName for StructName:
    fn required_method(self) -> Type:
        return implementation
```

## Dynamic Dispatch

```simple
let obj: dyn Trait = concrete_value  # TraitObject coercion
fn process(x: dyn Trait) -> Type     # Function parameter coercion
```

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/language/traits_spec.spl` | BDD spec (11 tests) |

## Dependencies

- Depends on: #12, #14
- Required by: None

## Notes

Traits enable polymorphism. dyn Trait creates TraitObjects for runtime dispatch.

# Static Polymorphism

*Source: `simple/std_lib/test/features/language/static_polymorphism_spec.spl`*

---

# Static Polymorphism

**Feature ID:** #2001
**Category:** Language
**Difficulty:** Level 4/5
**Status:** Complete
**Implementation:** Rust

## Overview

Interface bindings for static polymorphism via bind Interface = ImplType. Enables
compile-time dispatch for trait method calls, eliminating vtable lookup overhead.

## Syntax

```simple
trait Interface:
    fn method() -> Type

class Implementation:
    fn method() -> Type:
        return value

# Static dispatch via binding
bind Interface = Implementation

val obj: Interface = Implementation()
obj.method()  # Dispatches statically to Implementation::method
```

## Implementation

**Files:**
- src/compiler/src/monomorphize/binding_specializer.rs - Binding specialization
- src/compiler/src/interpreter_eval.rs - Static dispatch evaluation
- src/compiler/src/interpreter_method/special/objects.rs - Object method handling
- src/compiler/src/hir/types/module.rs - HIR type module
- src/compiler/src/mir/lower/lowering_core.rs - MIR lowering
- src/parser/src/ast/nodes/definitions.rs - AST definitions

**Tests:**
- tests/static_polymorphism_test.spl
- simple/std_lib/test/features/language/static_polymorphism_spec.spl

**Dependencies:** Feature #31
**Required By:** None

## Notes

Static polymorphism bindings are module-local. They enable dependency injection
patterns with zero runtime overhead.

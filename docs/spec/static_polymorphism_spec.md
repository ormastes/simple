# Static Polymorphism Specification

*Source: `./tests/system/static_polymorphism_spec.spl`*

---

# Static Polymorphism Specification

## Overview
Static polymorphism allows binding a trait to a concrete implementation type
for compile-time dispatch. This provides:
- Zero runtime overhead (no vtable)
- Compile-time type checking
- Monomorphization of generic code
- Explicit control over dispatch strategy

## Syntax
```simple
# Bind a trait to an implementation
bind TraitName = ConcreteType

# Use the trait as a type
fn create_instance() -> TraitName:
    return ConcreteType()

# The type system treats TraitName as ConcreteType
```

## Default Behavior
By default, trait types use **dynamic dispatch** (vtable-based).
The `bind` statement enables **static dispatch** for a specific trait.

## Comparison

| Feature | Dynamic (default) | Static (bind) |
|---------|------------------|---------------|
| Dispatch | Runtime vtable | Compile-time |
| Overhead | Pointer indirection | Zero |
| Flexibility | Can swap implementations | Fixed at compile-time |
| Trait object | Yes | No |

### Scenario: Define a trait interface

A trait defines a contract that types can implement:
```
trait TraitName:
    fn method(self, arg: Type) -> ReturnType
```

### Scenario: Implement a trait for a concrete type

A class can implement a trait by defining all required methods:

### Scenario: Bind trait to concrete type for static dispatch

The `bind` statement creates a compile-time association between
a trait and a specific implementation:
```
bind Logger = ConsoleLogger
```

After binding:
- `Logger` becomes an alias for `ConsoleLogger`
- All method calls on `Logger` dispatch directly to `ConsoleLogger`
- No vtable or runtime overhead

### Scenario: Function returns trait type with static binding

When a trait is bound to a concrete type, functions can return
the trait type and the compiler treats it as the concrete type:

### Scenario: Method call dispatches statically

With static binding, method calls are resolved at compile-time
directly to the bound implementation:

### Scenario: Type inference recognizes static binding

The type system should infer that `Logger` is `ConsoleLogger`
when the binding is active:

### Scenario: Generic function monomorphized with static binding

Generic functions that use trait bounds should be monomorphized
when the trait has a static binding:
```
fn generic<T: Logger>(logger: T) -> str:
    return logger.log("Message")
```

With `bind Logger = ConsoleLogger`, the function is specialized
to `ConsoleLogger` at compile-time.

### Scenario: Multiple implementations exist but one is bound

Even with static binding, multiple implementations can exist.
The binding only affects code using the trait type directly:

### Scenario: Type annotation uses statically bound trait

When variables are annotated with the trait type, the binding
determines the concrete type:

### Scenario: Function return type uses bound trait

Functions declared to return the trait type actually return
the bound concrete type:

### Scenario: Binding enforces compile-time type constraints

With static binding, attempting to return a different implementation
should cause a compile error:

### Scenario: Static dispatch has zero runtime cost

The generated code for static binding should:
- Have no vtable lookup
- Have no pointer indirection
- Be equivalent to direct function call
- Be fully inlinable

This is verified through code generation inspection.

### Scenario: Compare dynamic (default) and static (bind) dispatch

Default behavior uses dynamic dispatch:
```
trait Trait:
    fn method(self)

# No binding - uses dynamic dispatch
fn dynamic(t: Trait):
    t.method()  # Runtime dispatch via vtable
```

With binding, use static dispatch:
```
bind Trait = Impl

fn static(t: Trait):
    t.method()  # Compile-time dispatch to Impl.method
```

### Scenario: Generic trait bounds respect static binding

When a generic parameter has a trait bound and that trait has
a static binding, the generic is monomorphized to the bound type:
```
fn generic<T: Logger>(logger: T) -> str:
    return logger.log("msg")
```

With `bind Logger = ConsoleLogger`, this becomes:
```
fn generic(logger: ConsoleLogger) -> str:
    return logger.log("msg")
```

### Scenario: Static binding preserves associated types

If a trait has associated types, static binding should preserve
the concrete associated types from the bound implementation.

## Implementation Notes

### Lean Verification
The static polymorphism feature requires Lean verification for:
1. Type soundness - binding preserves type safety
2. Substitution correctness - bound types substitute properly
3. Monomorphization validity - generic specialization is sound
4. No vtable generation - static binding doesn't create vtables

### Type Inference Rules
```lean
-- Static binding creates type equality
Γ ⊢ bind T = C
-------------------
Γ ⊢ T ≡ C

-- Function return with binding
Γ ⊢ bind T = C    Γ ⊢ f : () → T
-----------------------------------
Γ ⊢ f : () → C

-- Method call with binding
Γ ⊢ bind T = C    Γ ⊢ x : T    Γ ⊢ C.m : (C, A) → B
------------------------------------------------------
Γ ⊢ x.m(a) : B
```

### Compiler Phases
1. **Parse**: Recognize `bind` statements
2. **Type Check**: Register trait-to-type binding
3. **Inference**: Substitute bound type for trait type
4. **HIR**: Lower trait types to concrete types
5. **MIR**: Generate direct calls (no vtable)
6. **Codegen**: Emit monomorphized code

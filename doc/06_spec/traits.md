# Simple Language Traits and Implementations - Test Specification

This spec covers Simple's trait system using local doubles that mirror the semantics without relying on unsupported surface syntax. Tests verify: defining traits, implementing them for types, static and dynamic dispatch, trait bounds, inheritance, associated types, coherence rules, and standard library traits (Clone, Eq, Hash, Debug).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #50-90 |
| Status | Executable coverage |
| Type | Extracted Examples (Category B) |
| Reference | traits.md |
| Source | `test/specs/traits_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Keywords:** traits, implementations, dispatch, generics, coherence
**Topics:** type-system, traits, polymorphism
**Symbols:** Trait, Impl, TraitObject, AssociatedType, Dispatch
**Module:** simple_compiler::traits

## Overview

This spec covers Simple's trait system using local doubles that mirror the
semantics without relying on unsupported surface syntax. Tests verify:
defining traits, implementing them for types, static and dynamic dispatch,
trait bounds, inheritance, associated types, coherence rules, and standard
library traits (Clone, Eq, Hash, Debug).

36 test cases covering the complete trait surface: definition, implementation,
dispatch modes, bounds, inheritance, associated types, trait objects, coherence,
blanket impls, and specialisation.

## Syntax

Define a trait and implement it for a type:

    trait Printable:
        fn display() -> text

    impl Printable for Person:
        fn display() -> text:
            "{self.name} ({self.age})"

Trait bounds on generics:

    fn print_all<T: Printable>(items: [T]):
        for item in items:
            println(item.display())

Trait inheritance:

    trait Drawable: Printable
        fn draw()

Associated type:

    trait Container:
        type Item
        fn first() -> Item

## Examples

    val person = Person.new("Ada", 37)
    person.display()    # => "Ada (37)"

    val registry = TraitRegistry.new()
    registry.define_trait("Printable")
    registry.implement("Printable", "Person")
    registry.has_impl("Printable", "Person")   # => true

    registry.inherit("Drawable", "Printable")
    registry.inherits("Drawable", "Printable") # => true

    registry.mark_marker("Clone")
    registry.is_marker("Clone")   # => true
    registry.is_marker("Display") # => false

## Key Concepts

**Traits** — named capability contracts. A trait declares method signatures
without providing implementations. Any type can implement a trait.

**Static dispatch** — when the concrete type is known at compile time, the
correct method is resolved with zero runtime overhead (monomorphisation).

**Dynamic dispatch** — `dyn Trait` (trait objects) allow heterogeneous
collections where the type is only known at runtime; dispatched via vtable.

**Coherence (orphan rule)** — a trait implementation must be defined either
in the crate that owns the trait or the crate that owns the type. This
prevents conflicting implementations.

**Blanket implementations** — implement a trait for all types satisfying
some bound: `impl<T: Display> Printable for T`.

**Marker traits** — traits with no methods; used to constrain generic bounds
(e.g., `Clone`, `Send`, `Sync`).

**Associated types** — a trait can declare abstract type members
(`type Item`) that implementers fill in, avoiding extra generic parameters.

**Interface bindings** — at a function boundary, declare which trait
implementation to use for a specific type, enabling static polymorphism
without dynamic dispatch cost.

## Common Patterns

Newtype wrapper that delegates trait implementations:

    class NewtypePerson:
        inner: Person
        fn display() -> text: self.inner.display()
        fn clone_name() -> text: self.inner.name

Default method implementations (override only what differs):

    trait Logger:
        fn log(msg: text)
        fn warn(msg: text): self.log("[warn] {msg}")
        fn error(msg: text): self.log("[error] {msg}")

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/traits/summary.txt` |

## Scenarios

- defining_a_trait_1
- defining_a_trait_2
- implementing_a_trait_3
- implementing_a_trait_4
- dispatch_5
- dispatch_6
- trait_bounds_and_generics_7
- trait_bounds_and_generics_8
- trait_bounds_and_generics_9
- trait_inheritance_10
- associated_types_11
- trait_objects_and_collections_12
- common_standard_traits_13
- note_on_semantic_types_14
- interface_bindings_static_polymorphism_15
- interface_bindings_static_polymorphism_16
- collection_traits_17
- inherent_impl_blocks_18
- inherent_impl_blocks_19
- inherent_impl_blocks_20
- inherent_impl_blocks_21
- inherent_impl_blocks_22
- trait_coherence_rules_23
- trait_coherence_rules_24
- trait_coherence_rules_25
- trait_coherence_rules_26
- trait_coherence_rules_27
- trait_coherence_rules_28
- trait_coherence_rules_29
- trait_coherence_rules_30
- trait_coherence_rules_31
- related_specifications_32
- related_specifications_33
- related_specifications_34
- related_specifications_35
- related_specifications_36

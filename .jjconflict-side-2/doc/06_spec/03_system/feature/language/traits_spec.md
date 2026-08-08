# Simple Language Traits and Implementations - Test Specification

> This spec covers Simple's trait system using local doubles that mirror the semantics without relying on unsupported surface syntax. Tests verify: defining traits, implementing them for types, static and dynamic dispatch, trait bounds, inheritance, associated types, coherence rules, and standard library traits (Clone, Eq, Hash, Debug).

<!-- sdn-diagram:id=traits_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traits_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traits_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traits_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Traits and Implementations - Test Specification

This spec covers Simple's trait system using local doubles that mirror the semantics without relying on unsupported surface syntax. Tests verify: defining traits, implementing them for types, static and dynamic dispatch, trait bounds, inheritance, associated types, coherence rules, and standard library traits (Clone, Eq, Hash, Debug).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #50-90 |
| Category | Other |
| Status | Executable coverage |
| Type | Extracted Examples (Category B) |
| Reference | traits.md |
| Source | `test/03_system/feature/language/traits_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Traits Spec

#### defining_a_trait_1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
expect(registry.define_trait("Printable")).to_equal(true)
expect(registry.has_trait("Printable")).to_equal(true)
```

</details>

#### defining_a_trait_2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
expect(registry.define_trait("Comparable")).to_equal(true)
expect(registry.set_assoc("Comparable", "Self")).to_equal(true)
expect(registry.assoc_type_for("Comparable")).to_equal("Self")
```

</details>

#### implementing_a_trait_3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
val person = Person.new("Ada", 37)
expect(registry.implement("Printable", "Person")).to_equal(true)
expect(accept_printable(registry, person)).to_equal("Ada (37)")
```

</details>

#### implementing_a_trait_4

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
val person = Person.new("Ada", 37)
expect(registry.implement("Printable", "Person")).to_equal(true)
expect(registry.implement("Debuggable", "Person")).to_equal(true)
expect(registry.impl_count("Printable")).to_equal(1)
expect(registry.impl_count("Debuggable")).to_equal(1)
expect(accept_printable_and_debuggable(registry, person)).to_contain("Ada (37)")
```

</details>

#### dispatch_5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val person = Person.new("Ada", 37)
expect(person.printable()).to_equal("Ada (37)")
```

</details>

#### dispatch_6

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = TraitObject.new("Printable", "Ada (37)")
expect(dynamic_dispatch(obj)).to_equal("Ada (37)")
```

</details>

#### trait_bounds_and_generics_7

1. registry implement
   - Expected: accept_printable(registry, person) equals `Ada (37)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
val person = Person.new("Ada", 37)
registry.implement("Printable", "Person")
expect(accept_printable(registry, person)).to_equal("Ada (37)")
```

</details>

#### trait_bounds_and_generics_8

1. registry implement
2. registry implement
   - Expected: where_clause_accepts(registry, person) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
val person = Person.new("Ada", 37)
registry.implement("Printable", "Person")
registry.implement("Debuggable", "Person")
expect(accept_printable_and_debuggable(registry, person)).to_contain("Ada (37)")
expect(where_clause_accepts(registry, person)).to_equal(true)
```

</details>

#### trait_bounds_and_generics_9

1. registry implement
2. registry implement
   - Expected: where_clause_accepts(registry, person) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
val person = Person.new("Ada", 37)
registry.implement("Printable", "Person")
registry.implement("Debuggable", "Person")
expect(where_clause_accepts(registry, person)).to_equal(true)
```

</details>

#### trait_inheritance_10

1. registry define trait
2. registry define trait
3. registry inherit
   - Expected: registry.inherits("Drawable", "Printable") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.define_trait("Printable")
registry.define_trait("Drawable")
registry.inherit("Drawable", "Printable")
expect(registry.inherits("Drawable", "Printable")).to_equal(true)
```

</details>

#### associated_types_11

1. registry set assoc
   - Expected: registry.assoc_type_for("Container") equals `Item`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.set_assoc("Container", "Item")
expect(registry.assoc_type_for("Container")).to_equal("Item")
```

</details>

#### trait_objects_and_collections_12

1. TraitObject new
2. TraitObject new
   - Expected: trait_object_list_description(items) equals `one,debug:two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [
    TraitObject.new("Printable", "one"),
    TraitObject.new("Debuggable", "two")
]
expect(trait_object_list_description(items)).to_equal("one,debug:two")
```

</details>

#### common_standard_traits_13

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = Record.new("alpha", 3)
val right = Record.new("alpha", 3)
expect(left.equals(right)).to_equal(true)
expect(left.clone_record().debug_text()).to_equal("Record(alpha, 3)")
expect(left.hash_value()).to_equal(right.hash_value())
```

</details>

#### note_on_semantic_types_14

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = SemanticMeters.new(3)
val right = SemanticMeters.new(7)
expect(left.add(right).as_text()).to_equal("10m")
```

</details>

#### interface_bindings_static_polymorphism_15

1. registry bind
   - Expected: registry.has_binding("Printable", "Person") is true
   - Expected: dispatch_mode(registry, "Printable") equals `static`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.bind("Printable", "Person")
expect(registry.has_binding("Printable", "Person")).to_equal(true)
expect(dispatch_mode(registry, "Printable")).to_equal("static")
```

</details>

#### interface_bindings_static_polymorphism_16

1. registry bind
   - Expected: registry.has_binding("Logger", "ConsoleLogger") is true
   - Expected: logger.log("ready") equals `[info] ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.bind("Logger", "ConsoleLogger")
expect(registry.has_binding("Logger", "ConsoleLogger")).to_equal(true)
val logger = Logger.new("[info] ")
expect(logger.log("ready")).to_equal("[info] ready")
```

</details>

#### collection_traits_17

1. seq add
2. seq add
   - Expected: seq.len() equals `2`
   - Expected: seq.join(",") equals `a,b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = SequenceBox.new()
seq.add("a")
seq.add("b")
expect(seq.len()).to_equal(2)
expect(seq.join(",")).to_equal("a,b")
```

</details>

#### inherent_impl_blocks_18

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val point = Point.new(2, 3)
expect(point.manhattan()).to_equal(5)
expect(point.shift(1, 1).debug_text()).to_equal("Point(3, 4)")
```

</details>

#### inherent_impl_blocks_19

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_box = WrapperText.new("hello")
expect(text_box.unwrap_text()).to_equal("hello")
```

</details>

#### inherent_impl_blocks_20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val person = Person.new("Ada", 37)
val boxed = NewtypePerson.new(person)
expect(boxed.display()).to_equal("Ada (37)")
```

</details>

#### inherent_impl_blocks_21

1. slice push
2. slice push
   - Expected: slice.first() equals `x`
   - Expected: slice.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slice = SliceBox.new()
slice.push("x")
slice.push("y")
expect(slice.first()).to_equal("x")
expect(slice.len()).to_equal(2)
```

</details>

#### inherent_impl_blocks_22

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val person = Person.new("Ada", 37)
expect(person.printable()).to_equal("Ada (37)")
expect(person.debug_text()).to_contain("Person")
```

</details>

#### trait_coherence_rules_23

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(can_orphan_implement("external", "local")).to_equal(true)
expect(can_orphan_implement("external", "external")).to_equal(false)
```

</details>

#### trait_coherence_rules_24

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
expect(registry.implement("Printable", "Person")).to_equal(true)
expect(registry.implement("Printable", "Person")).to_equal(false)
```

</details>

#### trait_coherence_rules_25

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
expect(registry.add_specialization("Printable", "Admin")).to_equal(true)
expect(registry.has_specialization("Printable", "Admin")).to_equal(true)
```

</details>

#### trait_coherence_rules_26

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
expect(registry.add_blanket("Printable")).to_equal(true)
expect(registry.is_blanket("Printable")).to_equal(true)
```

</details>

#### trait_coherence_rules_27

1. registry set assoc
   - Expected: registry.assoc_type_for("Container") equals `Item`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.set_assoc("Container", "Item")
expect(registry.assoc_type_for("Container")).to_equal("Item")
```

</details>

#### trait_coherence_rules_28

1. registry mark marker
   - Expected: registry.is_marker("Clone") is true
   - Expected: registry.is_marker("Display") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.mark_marker("Clone")
expect(registry.is_marker("Clone")).to_equal(true)
expect(registry.is_marker("Display")).to_equal(false)
```

</details>

#### trait_coherence_rules_29

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val person = Person.new("Ada", 37)
val wrapped = NewtypePerson.new(person)
expect(wrapped.display()).to_equal("Ada (37)")
```

</details>

#### trait_coherence_rules_30

1. registry define trait
2. registry implement
   - Expected: registry.has_impl("Printable", "Person") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.define_trait("Printable")
registry.implement("Printable", "Person")
expect(registry.has_impl("Printable", "Person")).to_equal(true)
```

</details>

#### trait_coherence_rules_31

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val person = Person.new("Ada", 37)
expect(person.clone_name()).to_equal("Ada")
expect(person.same_as(Person.new("Ada", 37))).to_equal(true)
```

</details>

#### related_specifications_32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
expect(registry.has_impl("Private", "Secret")).to_equal(false)
expect(registry.has_trait("Private")).to_equal(false)
```

</details>

#### related_specifications_33

1. registry add blanket
2. registry implement
   - Expected: registry.is_blanket("Printable") is true
   - Expected: registry.has_impl("Printable", "Any") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.add_blanket("Printable")
registry.implement("Printable", "Any")
expect(registry.is_blanket("Printable")).to_equal(true)
expect(registry.has_impl("Printable", "Any")).to_equal(true)
```

</details>

#### related_specifications_34

1. serializer exclude
   - Expected: serialize_record(serializer, "DisplayOnly", record) equals `excluded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serializer = Serializer.new()
serializer.exclude("DisplayOnly")
val record = Record.new("alpha", 3)
expect(serialize_record(serializer, "DisplayOnly", record)).to_equal("excluded")
```

</details>

#### related_specifications_35

1. registry mark marker
   - Expected: registry.is_marker("Send") is true
   - Expected: registry.is_marker("Display") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.mark_marker("Send")
expect(registry.is_marker("Send")).to_equal(true)
expect(registry.is_marker("Display")).to_equal(false)
```

</details>

#### related_specifications_36

1. registry define trait
2. registry implement
3. registry add specialization
   - Expected: registry.has_impl("Printable", "Person") is true
   - Expected: registry.has_specialization("Printable", "Admin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = TraitRegistry.new()
registry.define_trait("Printable")
registry.implement("Printable", "Person")
registry.add_specialization("Printable", "Admin")
expect(registry.has_impl("Printable", "Person")).to_equal(true)
expect(registry.has_specialization("Printable", "Admin")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

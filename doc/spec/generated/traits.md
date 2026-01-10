# Simple Language Traits and Implementations - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/traits_spec.spl`
> **Generated:** 2026-01-10 04:47:40
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/traits_spec.spl
> ```

**Status:** ✅ Implemented (uses existing coherence rules)
**Feature IDs:** **Source:** traits.md
**Note:** This is a test extraction file. For complete specification text,

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (36 tests)
- [Source Code](#source-code)

## Overview

This file contains executable test cases extracted from traits.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/traits.md

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `ALLOWED` | [20](#inherent_impl_blocks_20), [23](#trait_coherence_rules_23) |
| `Add` | [17](#collection_traits_17), [21](#inherent_impl_blocks_21) |
| `Alice` | [5](#unnamed_test), [12](#trait_objects_and_collections_12), [22](#inherent_impl_blocks_22) |
| `And` | [12](#trait_objects_and_collections_12) |
| `Any` | [10](#trait_inheritance_10) |
| `Array` | [17](#collection_traits_17) |
| `Associated` | [11](#associated_types_11), [18](#inherent_impl_blocks_18) |
| `AssociatedTypes` | [11](#associated_types_11) |
| `Bind` | [16](#interface_bindings_static_polymorphism_16) |
| `Bindings` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `Blanket` | [26](#trait_coherence_rules_26) |
| `Blocks` | [18](#inherent_impl_blocks_18), [19](#inherent_impl_blocks_19), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21), [22](#inherent_impl_blocks_22) |
| `Cannot` | [27](#trait_coherence_rules_27) |
| `Clone` | [13](#common_standard_traits_13), [17](#collection_traits_17), [24](#trait_coherence_rules_24), [28](#trait_coherence_rules_28), [32](#related_specifications_32), ... (7 total) |
| `Coherence` | [23](#trait_coherence_rules_23), [24](#trait_coherence_rules_24), [25](#trait_coherence_rules_25), [26](#trait_coherence_rules_26), [27](#trait_coherence_rules_27), ... (9 total) |
| `Collection` | [17](#collection_traits_17) |
| `CollectionTraits` | [17](#collection_traits_17) |
| `Collections` | [12](#trait_objects_and_collections_12) |
| `Common` | [13](#common_standard_traits_13) |
| `CommonStandardTraits` | [13](#common_standard_traits_13) |
| `Comparable` | [2](#defining_a_trait_2), [4](#implementing_a_trait_4), [8](#unnamed_test), [9](#unnamed_test) |
| `Compiler` | [5](#unnamed_test) |
| `Console` | [16](#interface_bindings_static_polymorphism_16) |
| `ConsoleLogger` | [16](#interface_bindings_static_polymorphism_16) |
| `Container` | [11](#associated_types_11), [27](#trait_coherence_rules_27) |
| `Copy` | [28](#trait_coherence_rules_28), [32](#related_specifications_32), [33](#related_specifications_33) |
| `Debug` | [13](#common_standard_traits_13), [26](#trait_coherence_rules_26) |
| `Default` | [17](#collection_traits_17), [33](#related_specifications_33), [36](#related_specifications_36) |
| `Define` | [20](#inherent_impl_blocks_20), [30](#trait_coherence_rules_30) |
| `Defining` | [1](#defining_a_trait_1), [2](#defining_a_trait_2) |
| `DefiningATrait` | [1](#defining_a_trait_1), [2](#defining_a_trait_2) |
| `Different` | [22](#inherent_impl_blocks_22) |
| `Dispatch` | [6](#dispatch_6) |
| `Display` | [23](#trait_coherence_rules_23), [34](#related_specifications_34) |
| `Drawable` | [10](#trait_inheritance_10) |
| `Dynamic` | [6](#dispatch_6), [12](#trait_objects_and_collections_12) |
| `ERROR` | [23](#trait_coherence_rules_23), [24](#trait_coherence_rules_24), [27](#trait_coherence_rules_27) |
| `Each` | [27](#trait_coherence_rules_27) |
| `FORBIDDEN` | [23](#trait_coherence_rules_23) |
| `File` | [16](#interface_bindings_static_polymorphism_16) |
| `FileLogger` | [16](#interface_bindings_static_polymorphism_16) |
| `For` | [34](#related_specifications_34) |
| `ForeignTrait` | [29](#trait_coherence_rules_29) |
| `ForeignType` | [31](#trait_coherence_rules_31) |
| `GOOD` | [14](#note_on_semantic_types_14) |
| `Growable` | [17](#collection_traits_17) |
| `Hash` | [13](#common_standard_traits_13) |
| `Hello` | [16](#interface_bindings_static_polymorphism_16), [19](#inherent_impl_blocks_19) |
| `Impl` | [18](#inherent_impl_blocks_18), [19](#inherent_impl_blocks_19), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21), [22](#inherent_impl_blocks_22) |
| `ImplTypeName` | [15](#interface_bindings_static_polymorphism_15) |
| `Implement` | [20](#inherent_impl_blocks_20) |
| `Implementing` | [3](#implementing_a_trait_3), [4](#implementing_a_trait_4), [23](#trait_coherence_rules_23) |
| `ImplementingATrait` | [3](#implementing_a_trait_3), [4](#implementing_a_trait_4) |
| `Inherent` | [18](#inherent_impl_blocks_18), [19](#inherent_impl_blocks_19), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21), [22](#inherent_impl_blocks_22) |
| `InherentImplBlocks` | [18](#inherent_impl_blocks_18), [19](#inherent_impl_blocks_19), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21), [22](#inherent_impl_blocks_22) |
| `Inheritance` | [10](#trait_inheritance_10) |
| `IntList` | [11](#associated_types_11), [27](#trait_coherence_rules_27) |
| `Interface` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `InterfaceBindingsStaticPolymorphism` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `Item` | [11](#associated_types_11), [14](#note_on_semantic_types_14), [27](#trait_coherence_rules_27) |
| `Iterator` | [14](#note_on_semantic_types_14) |
| `JSON` | [22](#inherent_impl_blocks_22) |
| `JsonExt` | [22](#inherent_impl_blocks_22) |
| `List` | [7](#unnamed_test), [8](#unnamed_test), [17](#collection_traits_17) |
| `Logger` | [16](#interface_bindings_static_polymorphism_16) |
| `Multiple` | [32](#related_specifications_32) |
| `MutSequence` | [17](#collection_traits_17) |
| `MyString` | [29](#trait_coherence_rules_29) |
| `MyTrait` | [23](#trait_coherence_rules_23) |
| `MyType` | [23](#trait_coherence_rules_23) |
| `MyWrapper` | [31](#trait_coherence_rules_31) |
| `NOT` | [32](#related_specifications_32), [35](#related_specifications_35) |
| `Negative` | [32](#related_specifications_32) |
| `Not` | [28](#trait_coherence_rules_28) |
| `Note` | [14](#note_on_semantic_types_14) |
| `NoteOnSemanticTypes` | [14](#note_on_semantic_types_14) |
| `Now` | [19](#inherent_impl_blocks_19), [29](#trait_coherence_rules_29) |
| `Objects` | [12](#trait_objects_and_collections_12) |
| `Only` | [17](#collection_traits_17), [35](#related_specifications_35) |
| `Option` | [14](#note_on_semantic_types_14), [17](#collection_traits_17) |
| `Ord` | [17](#collection_traits_17) |
| `Output` | [17](#collection_traits_17) |
| `Overlapping` | [24](#trait_coherence_rules_24) |
| `Person` | [3](#implementing_a_trait_3), [5](#unnamed_test), [12](#trait_objects_and_collections_12) |
| `Point` | [4](#implementing_a_trait_4), [12](#trait_objects_and_collections_12), [13](#common_standard_traits_13), [18](#inherent_impl_blocks_18) |
| `Polymorphism` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `Printable` | [1](#defining_a_trait_1), [3](#implementing_a_trait_3), [4](#implementing_a_trait_4), [5](#unnamed_test), [6](#dispatch_6), ... (11 total) |
| `Process` | [24](#trait_coherence_rules_24), [25](#trait_coherence_rules_25), [36](#related_specifications_36) |
| `Related` | [32](#related_specifications_32), [33](#related_specifications_33), [34](#related_specifications_34), [35](#related_specifications_35), [36](#related_specifications_36) |
| `RelatedSpecifications` | [32](#related_specifications_32), [33](#related_specifications_33), [34](#related_specifications_34), [35](#related_specifications_35), [36](#related_specifications_36) |
| `Result` | [14](#note_on_semantic_types_14) |
| `Rules` | [23](#trait_coherence_rules_23), [24](#trait_coherence_rules_24), [25](#trait_coherence_rules_25), [26](#trait_coherence_rules_26), [27](#trait_coherence_rules_27), ... (9 total) |
| `Safe` | [35](#related_specifications_35) |
| `SafeWrapper` | [32](#related_specifications_32) |
| `Self` | [2](#defining_a_trait_2), [11](#associated_types_11), [14](#note_on_semantic_types_14) |
| `Semantic` | [14](#note_on_semantic_types_14) |
| `Send` | [32](#related_specifications_32) |
| `Sequence` | [17](#collection_traits_17) |
| `Serialize` | [34](#related_specifications_34) |
| `Simple` | [33](#related_specifications_33) |
| `Slice` | [17](#collection_traits_17) |
| `SliceExt` | [21](#inherent_impl_blocks_21) |
| `Specialized` | [33](#related_specifications_33) |
| `Specific` | [36](#related_specifications_36) |
| `Specifications` | [32](#related_specifications_32), [33](#related_specifications_33), [34](#related_specifications_34), [35](#related_specifications_35), [36](#related_specifications_36) |
| `Standard` | [13](#common_standard_traits_13), [14](#note_on_semantic_types_14) |
| `Static` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `String` | [1](#defining_a_trait_1), [3](#implementing_a_trait_3), [4](#implementing_a_trait_4), [9](#unnamed_test), [10](#trait_inheritance_10), ... (14 total) |
| `StringExt` | [20](#inherent_impl_blocks_20), [30](#trait_coherence_rules_30) |
| `StringList` | [27](#trait_coherence_rules_27) |
| `Strings` | [19](#inherent_impl_blocks_19) |
| `Sync` | [32](#related_specifications_32) |
| `Trait` | [1](#defining_a_trait_1), [2](#defining_a_trait_2), [3](#implementing_a_trait_3), [4](#implementing_a_trait_4), [10](#trait_inheritance_10), ... (15 total) |
| `TraitCoherenceRules` | [23](#trait_coherence_rules_23), [24](#trait_coherence_rules_24), [25](#trait_coherence_rules_25), [26](#trait_coherence_rules_26), [27](#trait_coherence_rules_27), ... (9 total) |
| `TraitInheritance` | [10](#trait_inheritance_10) |
| `TraitName` | [15](#interface_bindings_static_polymorphism_15) |
| `TraitObjectsAndCollections` | [12](#trait_objects_and_collections_12) |
| `Traits` | [13](#common_standard_traits_13), [17](#collection_traits_17) |
| `Types` | [11](#associated_types_11), [14](#note_on_semantic_types_14) |
| `Unnamed` | [5](#unnamed_test), [7](#unnamed_test), [8](#unnamed_test), [9](#unnamed_test) |
| `UnsafePointer` | [35](#related_specifications_35) |
| `Usage` | [18](#inherent_impl_blocks_18), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21) |
| `Use` | [14](#note_on_semantic_types_14) |
| `User` | [14](#note_on_semantic_types_14), [22](#inherent_impl_blocks_22) |
| `UserId` | [14](#note_on_semantic_types_14) |
| `UserService` | [14](#note_on_semantic_types_14) |
| `UserStatus` | [14](#note_on_semantic_types_14) |
| `Uses` | [6](#dispatch_6) |
| `Widget` | [10](#trait_inheritance_10), [12](#trait_objects_and_collections_12) |
| `With` | [16](#interface_bindings_static_polymorphism_16), [25](#trait_coherence_rules_25) |
| `Works` | [17](#collection_traits_17), [20](#inherent_impl_blocks_20) |
| `World` | [19](#inherent_impl_blocks_19) |
| `Wrap` | [29](#trait_coherence_rules_29) |
| `XML` | [22](#inherent_impl_blocks_22) |
| `XmlExt` | [22](#inherent_impl_blocks_22) |
| `add` | [11](#associated_types_11) |
| `and` | [12](#trait_objects_and_collections_12) |
| `as_bytes` | [34](#related_specifications_34) |
| `assert_compiles` | [1](#defining_a_trait_1), [2](#defining_a_trait_2), [3](#implementing_a_trait_3), [4](#implementing_a_trait_4), [6](#dispatch_6), ... (32 total) |
| `associated` | [11](#associated_types_11) |
| `associated_types` | [11](#associated_types_11) |
| `binary_serialize` | [34](#related_specifications_34) |
| `bindings` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `blocks` | [18](#inherent_impl_blocks_18), [19](#inherent_impl_blocks_19), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21), [22](#inherent_impl_blocks_22) |
| `clone` | [17](#collection_traits_17), [28](#trait_coherence_rules_28), [33](#related_specifications_33) |
| `coherence` | [23](#trait_coherence_rules_23), [24](#trait_coherence_rules_24), [25](#trait_coherence_rules_25), [26](#trait_coherence_rules_26), [27](#trait_coherence_rules_27), ... (9 total) |
| `collection` | [17](#collection_traits_17) |
| `collection_traits` | [17](#collection_traits_17) |
| `collections` | [12](#trait_objects_and_collections_12) |
| `common` | [13](#common_standard_traits_13) |
| `common_standard_traits` | [13](#common_standard_traits_13) |
| `compare` | [2](#defining_a_trait_2), [4](#implementing_a_trait_4), [8](#unnamed_test) |
| `copy` | [32](#related_specifications_32) |
| `create_logger` | [16](#interface_bindings_static_polymorphism_16) |
| `debug_fmt` | [26](#trait_coherence_rules_26) |
| `deep_clone` | [33](#related_specifications_33) |
| `default` | [17](#collection_traits_17), [21](#inherent_impl_blocks_21) |
| `defining` | [1](#defining_a_trait_1), [2](#defining_a_trait_2) |
| `defining_a_trait` | [1](#defining_a_trait_1), [2](#defining_a_trait_2) |
| `delegate_method` | [31](#trait_coherence_rules_31) |
| `derive` | [13](#common_standard_traits_13) |
| `dispatch` | [6](#dispatch_6) |
| `distance` | [18](#inherent_impl_blocks_18) |
| `draw` | [10](#trait_inheritance_10) |
| `equals` | [2](#defining_a_trait_2) |
| `fmt` | [23](#trait_coherence_rules_23) |
| `fold` | [17](#collection_traits_17) |
| `function` | [18](#inherent_impl_blocks_18) |
| `get` | [11](#associated_types_11) |
| `get_user` | [14](#note_on_semantic_types_14) |
| `greater_than` | [2](#defining_a_trait_2) |
| `impl` | [18](#inherent_impl_blocks_18), [19](#inherent_impl_blocks_19), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21), [22](#inherent_impl_blocks_22) |
| `implementing` | [3](#implementing_a_trait_3), [4](#implementing_a_trait_4) |
| `implementing_a_trait` | [3](#implementing_a_trait_3), [4](#implementing_a_trait_4) |
| `inherent` | [18](#inherent_impl_blocks_18), [19](#inherent_impl_blocks_19), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21), [22](#inherent_impl_blocks_22) |
| `inherent_impl_blocks` | [18](#inherent_impl_blocks_18), [19](#inherent_impl_blocks_19), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21), [22](#inherent_impl_blocks_22) |
| `inheritance` | [10](#trait_inheritance_10) |
| `interface` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `interface_bindings_static_polymorphism` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `len` | [11](#associated_types_11), [20](#inherent_impl_blocks_20) |
| `less_than` | [2](#defining_a_trait_2) |
| `log` | [5](#unnamed_test), [16](#interface_bindings_static_polymorphism_16) |
| `main` | [16](#interface_bindings_static_polymorphism_16), [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21) |
| `max` | [17](#collection_traits_17) |
| `my_extension` | [30](#trait_coherence_rules_30) |
| `my_method` | [23](#trait_coherence_rules_23) |
| `new` | [18](#inherent_impl_blocks_18) |
| `next` | [14](#note_on_semantic_types_14) |
| `note` | [14](#note_on_semantic_types_14) |
| `note_on_semantic_types` | [14](#note_on_semantic_types_14) |
| `objects` | [12](#trait_objects_and_collections_12) |
| `origin` | [18](#inherent_impl_blocks_18) |
| `original_method` | [31](#trait_coherence_rules_31) |
| `polymorphism` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `print` | [20](#inherent_impl_blocks_20), [21](#inherent_impl_blocks_21), [22](#inherent_impl_blocks_22), [24](#trait_coherence_rules_24), [25](#trait_coherence_rules_25), ... (6 total) |
| `print_self` | [1](#defining_a_trait_1), [5](#unnamed_test), [6](#dispatch_6), [7](#unnamed_test), [8](#unnamed_test), ... (6 total) |
| `process` | [24](#trait_coherence_rules_24), [25](#trait_coherence_rules_25), [36](#related_specifications_36) |
| `push` | [11](#associated_types_11), [17](#collection_traits_17) |
| `related` | [32](#related_specifications_32), [33](#related_specifications_33), [34](#related_specifications_34), [35](#related_specifications_35), [36](#related_specifications_36) |
| `related_specifications` | [32](#related_specifications_32), [33](#related_specifications_33), [34](#related_specifications_34), [35](#related_specifications_35), [36](#related_specifications_36) |
| `return` | [18](#inherent_impl_blocks_18) |
| `reverse` | [17](#collection_traits_17) |
| `rules` | [23](#trait_coherence_rules_23), [24](#trait_coherence_rules_24), [25](#trait_coherence_rules_25), [26](#trait_coherence_rules_26), [27](#trait_coherence_rules_27), ... (9 total) |
| `semantic` | [14](#note_on_semantic_types_14) |
| `set_status` | [14](#note_on_semantic_types_14) |
| `sort` | [8](#unnamed_test) |
| `specifications` | [32](#related_specifications_32), [33](#related_specifications_33), [34](#related_specifications_34), [35](#related_specifications_35), [36](#related_specifications_36) |
| `split` | [20](#inherent_impl_blocks_20) |
| `sqrt` | [18](#inherent_impl_blocks_18) |
| `standard` | [13](#common_standard_traits_13) |
| `static` | [15](#interface_bindings_static_polymorphism_15), [16](#interface_bindings_static_polymorphism_16) |
| `stringify` | [1](#defining_a_trait_1), [3](#implementing_a_trait_3), [4](#implementing_a_trait_4), [9](#unnamed_test), [10](#trait_inheritance_10), ... (6 total) |
| `sum` | [21](#inherent_impl_blocks_21) |
| `to_bytes` | [34](#related_specifications_34) |
| `to_json` | [22](#inherent_impl_blocks_22) |
| `to_string` | [34](#related_specifications_34) |
| `to_title_case` | [19](#inherent_impl_blocks_19), [20](#inherent_impl_blocks_20) |
| `to_xml` | [22](#inherent_impl_blocks_22) |
| `trait` | [1](#defining_a_trait_1), [2](#defining_a_trait_2), [3](#implementing_a_trait_3), [4](#implementing_a_trait_4), [10](#trait_inheritance_10), ... (15 total) |
| `trait_coherence_rules` | [23](#trait_coherence_rules_23), [24](#trait_coherence_rules_24), [25](#trait_coherence_rules_25), [26](#trait_coherence_rules_26), [27](#trait_coherence_rules_27), ... (9 total) |
| `trait_inheritance` | [10](#trait_inheritance_10) |
| `trait_objects_and_collections` | [12](#trait_objects_and_collections_12) |
| `traits` | [13](#common_standard_traits_13), [17](#collection_traits_17) |
| `types` | [11](#associated_types_11), [14](#note_on_semantic_types_14), [33](#related_specifications_33) |
| `unnamed` | [5](#unnamed_test), [7](#unnamed_test), [8](#unnamed_test), [9](#unnamed_test) |
| `word_count` | [20](#inherent_impl_blocks_20) |

---

## Test Cases (36 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [defining_a_trait_1](#defining_a_trait_1) | Defining a Trait | `trait`, `defining`, `defining_a_trait` +8 |
| 2 | [defining_a_trait_2](#defining_a_trait_2) | Defining a Trait | `trait`, `defining`, `defining_a_trait` +10 |
| 3 | [implementing_a_trait_3](#implementing_a_trait_3) | Implementing a Trait | `implementing`, `trait`, `Trait` +8 |
| 4 | [implementing_a_trait_4](#implementing_a_trait_4) | Implementing a Trait | `implementing`, `trait`, `Trait` +10 |
| 5 | [unnamed_test](#unnamed_test) | Dispatch | `unnamed`, `Unnamed`, `print_self` +5 |
| 6 | [dispatch_6](#dispatch_6) | Dispatch | `Dispatch`, `dispatch`, `assert_compiles` +4 |
| 7 | [unnamed_test](#unnamed_test) | Trait Bounds and Generics | `unnamed`, `Unnamed`, `print_self` +2 |
| 8 | [unnamed_test](#unnamed_test) | Trait Bounds and Generics | `unnamed`, `Unnamed`, `print_self` +5 |
| 9 | [unnamed_test](#unnamed_test) | Trait Bounds and Generics | `unnamed`, `Unnamed`, `stringify` +3 |
| 10 | [trait_inheritance_10](#trait_inheritance_10) | Trait Inheritance | `trait`, `Trait`, `Inheritance` +11 |
| 11 | [associated_types_11](#associated_types_11) | Associated Types | `types`, `Types`, `associated_types` +12 |
| 12 | [trait_objects_and_collections_12](#trait_objects_and_collections_12) | Trait Objects and Collections | `trait`, `objects`, `and` +15 |
| 13 | [common_standard_traits_13](#common_standard_traits_13) | Common Standard Traits | `Common`, `traits`, `Traits` +11 |
| 14 | [note_on_semantic_types_14](#note_on_semantic_types_14) | Note on Semantic Types | `types`, `Types`, `Note` +21 |
| 15 | [interface_bindings_static_polymorphism_15](#interface_bindings_static_polymorphism_15) | Interface Bindings (Static Polymorphism) | `interface`, `InterfaceBindingsStaticPolymorphism`, `bindings` +10 |
| 16 | [interface_bindings_static_polymorphism_16](#interface_bindings_static_polymorphism_16) | Interface Bindings (Static Polymorphism) | `interface`, `InterfaceBindingsStaticPolymorphism`, `bindings` +19 |
| 17 | [collection_traits_17](#collection_traits_17) | Collection Traits | `traits`, `Traits`, `CollectionTraits` +25 |
| 18 | [inherent_impl_blocks_18](#inherent_impl_blocks_18) | Inherent Impl Blocks | `inherent`, `Impl`, `Inherent` +15 |
| 19 | [inherent_impl_blocks_19](#inherent_impl_blocks_19) | Inherent Impl Blocks | `inherent`, `Impl`, `Inherent` +12 |
| 20 | [inherent_impl_blocks_20](#inherent_impl_blocks_20) | Inherent Impl Blocks | `inherent`, `Impl`, `Inherent` +19 |
| 21 | [inherent_impl_blocks_21](#inherent_impl_blocks_21) | Inherent Impl Blocks | `inherent`, `Impl`, `Inherent` +13 |
| 22 | [inherent_impl_blocks_22](#inherent_impl_blocks_22) | Inherent Impl Blocks | `inherent`, `Impl`, `Inherent` +17 |
| 23 | [trait_coherence_rules_23](#trait_coherence_rules_23) | Trait Coherence Rules | `coherence`, `trait`, `Trait` +16 |
| 24 | [trait_coherence_rules_24](#trait_coherence_rules_24) | Trait Coherence Rules | `coherence`, `trait`, `Trait` +12 |
| 25 | [trait_coherence_rules_25](#trait_coherence_rules_25) | Trait Coherence Rules | `coherence`, `trait`, `Trait` +10 |
| 26 | [trait_coherence_rules_26](#trait_coherence_rules_26) | Trait Coherence Rules | `coherence`, `trait`, `Trait` +12 |
| 27 | [trait_coherence_rules_27](#trait_coherence_rules_27) | Trait Coherence Rules | `coherence`, `trait`, `Trait` +14 |
| 28 | [trait_coherence_rules_28](#trait_coherence_rules_28) | Trait Coherence Rules | `coherence`, `trait`, `Trait` +10 |
| 29 | [trait_coherence_rules_29](#trait_coherence_rules_29) | Trait Coherence Rules | `coherence`, `trait`, `Trait` +11 |
| 30 | [trait_coherence_rules_30](#trait_coherence_rules_30) | Trait Coherence Rules | `coherence`, `trait`, `Trait` +10 |
| 31 | [trait_coherence_rules_31](#trait_coherence_rules_31) | Trait Coherence Rules | `coherence`, `trait`, `Trait` +10 |
| 32 | [related_specifications_32](#related_specifications_32) | Related Specifications | `Related`, `specifications`, `related_specifications` +13 |
| 33 | [related_specifications_33](#related_specifications_33) | Related Specifications | `Related`, `specifications`, `related_specifications` +12 |
| 34 | [related_specifications_34](#related_specifications_34) | Related Specifications | `Related`, `specifications`, `related_specifications` +11 |
| 35 | [related_specifications_35](#related_specifications_35) | Related Specifications | `Related`, `specifications`, `related_specifications` +8 |
| 36 | [related_specifications_36](#related_specifications_36) | Related Specifications | `Related`, `specifications`, `related_specifications` +10 |

---

### Test 1: Defining a Trait {#defining_a_trait_1}

*Source line: ~3*

**Test name:** `defining_a_trait_1`

**Linked Symbols:**
- `trait`
- `defining`
- `defining_a_trait`
- `Trait`
- `DefiningATrait`
- `Defining`
- `assert_compiles`
- `print_self`
- `Printable`
- `String`
- ... and 1 more

**Code:**

```simple
test "defining_a_trait_1":
    trait Printable:
        fn stringify() -> String
        fn print_self():
            # default implementation
            print self.stringify()
    assert_compiles()
```

### Test 2: Defining a Trait {#defining_a_trait_2}

*Source line: ~19*

**Test name:** `defining_a_trait_2`

**Description:**

The special `self` keyword in trait definitions refers to the implementing instance type (like `Self...

**Linked Symbols:**
- `trait`
- `defining`
- `defining_a_trait`
- `Trait`
- `DefiningATrait`
- `Defining`
- `less_than`
- `greater_than`
- `assert_compiles`
- `equals`
- ... and 3 more

**Code:**

```simple
test "defining_a_trait_2":
    trait Comparable:
        fn compare(other: Self) -> i32
        fn equals(other: Self) -> bool:
            return self.compare(other) == 0
        fn less_than(other: Self) -> bool:
            return self.compare(other) < 0
        fn greater_than(other: Self) -> bool:
            return self.compare(other) > 0
    assert_compiles()
```

### Test 3: Implementing a Trait {#implementing_a_trait_3}

*Source line: ~5*

**Test name:** `implementing_a_trait_3`

**Description:**

To implement a trait for a type, use an `impl Trait for Type` block:

**Linked Symbols:**
- `implementing`
- `trait`
- `Trait`
- `Implementing`
- `implementing_a_trait`
- `ImplementingATrait`
- `assert_compiles`
- `Printable`
- `Person`
- `String`
- ... and 1 more

**Code:**

```simple
test "implementing_a_trait_3":
    struct Person:
        name: String
        age: i32

    impl Printable for Person:
        fn stringify() -> String:
            return "{self.name} (age {self.age})"
        # print_self uses the trait's default implementation
    assert_compiles()
```

### Test 4: Implementing a Trait {#implementing_a_trait_4}

*Source line: ~22*

**Test name:** `implementing_a_trait_4`

**Description:**

A type can implement any number of traits:

**Linked Symbols:**
- `implementing`
- `trait`
- `Trait`
- `Implementing`
- `implementing_a_trait`
- `ImplementingATrait`
- `Point`
- `assert_compiles`
- `Comparable`
- `Printable`
- ... and 3 more

**Code:**

```simple
test "implementing_a_trait_4":
    struct Point:
        x: f64
        y: f64

    impl Printable for Point:
        fn stringify() -> String:
            return "({self.x}, {self.y})"

    impl Comparable for Point:
        fn compare(other: Point) -> i32:
            let d1 = self.x * self.x + self.y * self.y
            let d2 = other.x * other.x + other.y * other.y
            if d1 < d2: return -1
            if d1 > d2: return 1
            return 0
    assert_compiles()
```

### Test 5: Dispatch {#unnamed_test}

*Source line: ~7*

**Test name:** `unnamed_test`

**Description:**

Traits support static dispatch by default - the compiler knows at compile time the exact type and ca...

**Linked Symbols:**
- `unnamed`
- `Unnamed`
- `print_self`
- `log`
- `Printable`
- `Person`
- `Compiler`
- `Alice`

**Code:**

```simple
fn log[T: Printable](item: T):
    item.print_self()

let p = Person(name: "Alice", age: 30)
log(p)  # Compiler knows T = Person
```

### Test 6: Dispatch {#dispatch_6}

*Source line: ~21*

**Test name:** `dispatch_6`

**Description:**

For cases where the concrete type isn't known at compile time, traits use dynamic dispatch by defaul...

**Linked Symbols:**
- `Dispatch`
- `dispatch`
- `assert_compiles`
- `print_self`
- `Dynamic`
- `Printable`
- `Uses`

**Code:**

```simple
test "dispatch_6":
    let x: Printable = somePrintableObject  # Uses vtable
    x.print_self()  # Dynamic dispatch
    assert_compiles()
```

### Test 7: Trait Bounds and Generics {#unnamed_test}

*Source line: ~5*

**Test name:** `unnamed_test`

**Description:**

Traits are often used as bounds on type parameters:

**Linked Symbols:**
- `unnamed`
- `Unnamed`
- `print_self`
- `List`
- `Printable`

**Code:**

```simple
fn print_all[T: Printable](items: List[T]):
    for item in items:
        item.print_self()
```

### Test 8: Trait Bounds and Generics {#unnamed_test}

*Source line: ~15*

**Test name:** `unnamed_test`

**Description:**

This generic function `print_all` can accept a list of any type `T` that implements `Printable`. The...

**Linked Symbols:**
- `unnamed`
- `Unnamed`
- `print_self`
- `Comparable`
- `Printable`
- `List`
- `compare`
- `sort`

**Code:**

```simple
fn process[T: Printable + Comparable](items: List[T]):
    for item in items:
        item.print_self()
    items.sort(\a, b: a.compare(b))
```

### Test 9: Trait Bounds and Generics {#unnamed_test}

*Source line: ~28*

**Test name:** `unnamed_test`

**Description:**

For complex bounds, use where clauses:

**Linked Symbols:**
- `unnamed`
- `Unnamed`
- `stringify`
- `Comparable`
- `String`
- `Printable`

**Code:**

```simple
fn complex[T, U](a: T, b: U) -> String
    where T: Printable,
          U: Comparable + Printable:
    return "{a.stringify()} vs {b.stringify()}"
```

### Test 10: Trait Inheritance {#trait_inheritance_10}

*Source line: ~5*

**Test name:** `trait_inheritance_10`

**Description:**

One trait can require another:

**Linked Symbols:**
- `trait`
- `Trait`
- `Inheritance`
- `inheritance`
- `TraitInheritance`
- `trait_inheritance`
- `Drawable`
- `assert_compiles`
- `Printable`
- `Any`
- ... and 4 more

**Code:**

```simple
test "trait_inheritance_10":
    trait Drawable: Printable:
        fn draw()

    # Any Drawable must also be Printable
    impl Drawable for Widget:
        fn stringify() -> String:
            return "Widget"
        fn draw():
            # drawing code
    assert_compiles()
```

### Test 11: Associated Types {#associated_types_11}

*Source line: ~5*

**Test name:** `associated_types_11`

**Description:**

Traits can include associated type placeholders:

**Linked Symbols:**
- `types`
- `Types`
- `associated_types`
- `AssociatedTypes`
- `associated`
- `Associated`
- `Container`
- `len`
- `assert_compiles`
- `IntList`
- ... and 5 more

**Code:**

```simple
test "associated_types_11":
    trait Container:
        type Item
        fn add(item: Self.Item)
        fn get(index: i32) -> Self.Item?

    struct IntList:
        items: [i32]

    impl Container for IntList:
        type Item = i32
        fn add(item: i32):
            self.items.push(item)
        fn get(index: i32) -> i32?:
            if index < self.items.len():
                return Some(self.items[index])
            return None
    assert_compiles()
```

### Test 12: Trait Objects and Collections {#trait_objects_and_collections_12}

*Source line: ~5*

**Test name:** `trait_objects_and_collections_12`

**Description:**

Trait objects allow storing different types that implement the same trait:

**Linked Symbols:**
- `trait`
- `objects`
- `and`
- `Trait`
- `collections`
- `Collections`
- `Objects`
- `TraitObjectsAndCollections`
- `And`
- `trait_objects_and_collections`
- ... and 8 more

**Code:**

```simple
test "trait_objects_and_collections_12":
    let printables: [Printable] = [
        Person(name: "Alice", age: 30),
        Point(x: 1.0, y: 2.0),
        Widget("button"),
    ]

    for p in printables:
        p.print_self()  # Dynamic dispatch
    assert_compiles()
```

### Test 13: Common Standard Traits {#common_standard_traits_13}

*Source line: ~18*

**Test name:** `common_standard_traits_13`

**Description:**

Common traits can be automatically derived:

**Linked Symbols:**
- `Common`
- `traits`
- `Traits`
- `common`
- `standard`
- `CommonStandardTraits`
- `common_standard_traits`
- `Standard`
- `Clone`
- `Point`
- ... and 4 more

**Code:**

```simple
test "common_standard_traits_13":
    #[derive(Eq, Hash, Clone, Debug)]
    struct Point:
        x: f64
        y: f64
    assert_compiles()
```

### Test 14: Note on Semantic Types {#note_on_semantic_types_14}

*Source line: ~5*

**Test name:** `note_on_semantic_types_14`

**Description:**

Trait methods in public APIs should follow the same semantic type guidelines as regular functions:

**Linked Symbols:**
- `types`
- `Types`
- `Note`
- `NoteOnSemanticTypes`
- `note`
- `Semantic`
- `note_on_semantic_types`
- `semantic`
- `set_status`
- `next`
- ... and 14 more

**Code:**

```simple
test "note_on_semantic_types_14":
    # GOOD: Use semantic types in public trait methods
    trait UserService:
        fn get_user(id: UserId) -> Option[User]
        fn set_status(id: UserId, status: UserStatus)

    # Standard library traits use Option/Result
    trait Iterator:
        type Item
        fn next(self) -> Option[Self.Item]
    assert_compiles()
```

### Test 15: Interface Bindings (Static Polymorphism) {#interface_bindings_static_polymorphism_15}

*Source line: ~9*

**Test name:** `interface_bindings_static_polymorphism_15`

**Description:**

Important: The `bind` statement only supports static dispatch. There is no `static` or `dyn` keyword...

**Linked Symbols:**
- `interface`
- `InterfaceBindingsStaticPolymorphism`
- `bindings`
- `Bindings`
- `Interface`
- `interface_bindings_static_polymorphism`
- `Polymorphism`
- `Static`
- `polymorphism`
- `static`
- ... and 3 more

**Code:**

```simple
test "interface_bindings_static_polymorphism_15":
    bind TraitName = ImplTypeName
    assert_compiles()
```

### Test 16: Interface Bindings (Static Polymorphism) {#interface_bindings_static_polymorphism_16}

*Source line: ~15*

**Test name:** `interface_bindings_static_polymorphism_16`

**Description:**

```simple
bind TraitName = ImplTypeName
```

**Linked Symbols:**
- `interface`
- `InterfaceBindingsStaticPolymorphism`
- `bindings`
- `Bindings`
- `Interface`
- `interface_bindings_static_polymorphism`
- `Polymorphism`
- `Static`
- `polymorphism`
- `static`
- ... and 12 more

**Code:**

```simple
test "interface_bindings_static_polymorphism_16":
    trait Logger:
        fn log(self, msg: str) -> str

    class ConsoleLogger:
        fn log(self, msg: str) -> str:
            return "Console: " + msg

    class FileLogger:
        fn log(self, msg: str) -> str:
            return "File: " + msg

    # Bind Logger to ConsoleLogger for this module
    bind Logger = ConsoleLogger

    fn create_logger() -> Logger:
        return ConsoleLogger()

    fn main():
        let logger: Logger = create_logger()
        # With binding, this dispatches statically to ConsoleLogger::log
        # No vtable lookup required
        let result = logger.log("Hello")
        # result is "Console: Hello"
    assert_compiles()
```

### Test 17: Collection Traits {#collection_traits_17}

*Source line: ~46*

**Test name:** `collection_traits_17`

**Description:**

| Type | Iterable | Collection | Sequence | MutSequence | ImmutSequence | Growable | Sliceable |
|--...

**Linked Symbols:**
- `traits`
- `Traits`
- `CollectionTraits`
- `collection`
- `collection_traits`
- `Collection`
- `Slice`
- `Default`
- `push`
- `Add`
- ... and 18 more

**Code:**

```simple
test "collection_traits_17":
    # Works with List, Array, Slice, String
    fn sum[C: Sequence[T], T: Add[Output=T] + Default](seq: C) -> T:
        seq.fold(T::default(), |acc, x| acc + x)

    # Works with List and Array
    fn find_max[C: Sequence[T], T: Ord](seq: C) -> Option[T]:
        seq.max()

    # Works with any mutable sequence
    fn reverse_in_place[C: MutSequence[T], T](seq: &mut C):
        seq.reverse()

    # Only List (Growable) can use push
    fn append_all[C: Growable[T], T: Clone](dest: &mut C, items: Slice[T]):
        for item in items:
            dest.push(item.clone())
    assert_compiles()
```

### Test 18: Inherent Impl Blocks {#inherent_impl_blocks_18}

*Source line: ~5*

**Test name:** `inherent_impl_blocks_18`

**Description:**

Methods can be added directly to types without using traits:

**Linked Symbols:**
- `inherent`
- `Impl`
- `Inherent`
- `Blocks`
- `impl`
- `blocks`
- `InherentImplBlocks`
- `inherent_impl_blocks`
- `new`
- `distance`
- ... and 8 more

**Code:**

```simple
test "inherent_impl_blocks_18":
    struct Point:
        x: f64
        y: f64

    impl Point:
        fn new(x: f64, y: f64) -> Point:
            return Point(x: x, y: y)

        fn distance(self, other: Point) -> f64:
            let dx = self.x - other.x
            let dy = self.y - other.y
            return (dx * dx + dy * dy).sqrt()

        fn origin() -> Point:  # Associated function (no self)
            return Point(x: 0.0, y: 0.0)

    # Usage
    let p1 = Point.new(3.0, 4.0)
    let p2 = Point.origin()
    let d = p1.distance(p2)  # 5.0
    assert_compiles()
```

### Test 19: Inherent Impl Blocks {#inherent_impl_blocks_19}

*Source line: ~41*

**Test name:** `inherent_impl_blocks_19`

**Description:**

Extension methods allow adding methods to types defined elsewhere:

**Linked Symbols:**
- `inherent`
- `Impl`
- `Inherent`
- `Blocks`
- `impl`
- `blocks`
- `InherentImplBlocks`
- `inherent_impl_blocks`
- `Now`
- `Hello`
- ... and 5 more

**Code:**

```simple
test "inherent_impl_blocks_19":
    # In your module
    impl String:
        fn to_title_case(self) -> String:
            # implementation
            ...

    # Now all Strings have to_title_case()
    let title = "hello world".to_title_case()  # "Hello World"
    assert_compiles()
```

### Test 20: Inherent Impl Blocks {#inherent_impl_blocks_20}

*Source line: ~62*

**Test name:** `inherent_impl_blocks_20`

**Linked Symbols:**
- `inherent`
- `Impl`
- `Inherent`
- `Blocks`
- `impl`
- `blocks`
- `InherentImplBlocks`
- `inherent_impl_blocks`
- `split`
- `Define`
- ... and 12 more

**Code:**

```simple
test "inherent_impl_blocks_20":
    # Define a local extension trait
    trait StringExt:
        fn to_title_case(self) -> String
        fn word_count(self) -> i32

    # Implement for foreign type - ALLOWED because trait is local
    impl StringExt for String:
        fn to_title_case(self) -> String:
            # implementation
            return self  # simplified

        fn word_count(self) -> i32:
            return self.split(" ").len()

    # Usage
    fn main():
        let text = "hello world"
        print(text.to_title_case())  # Works!
        print(text.word_count())      # Works!
    assert_compiles()
```

### Test 21: Inherent Impl Blocks {#inherent_impl_blocks_21}

*Source line: ~100*

**Test name:** `inherent_impl_blocks_21`

**Description:**

Example - Extending Standard Types:

**Linked Symbols:**
- `inherent`
- `Impl`
- `Inherent`
- `Blocks`
- `impl`
- `blocks`
- `InherentImplBlocks`
- `inherent_impl_blocks`
- `main`
- `Add`
- ... and 6 more

**Code:**

```simple
test "inherent_impl_blocks_21":
    # In your crate
    trait SliceExt[T]:
        fn sum(self) -> T where T: Add

    impl[T: Add] SliceExt[T] for [T]:
        fn sum(self) -> T:
            let result = T::default()
            for item in self:
                result = result + item
            return result

    # Usage
    use my_extensions::SliceExt

    fn main():
        let numbers = [1, 2, 3, 4, 5]
        print(numbers.sum())  # 15
    assert_compiles()
```

### Test 22: Inherent Impl Blocks {#inherent_impl_blocks_22}

*Source line: ~122*

**Test name:** `inherent_impl_blocks_22`

**Description:**

Example - Multiple Extension Traits:

**Linked Symbols:**
- `inherent`
- `Impl`
- `Inherent`
- `Blocks`
- `impl`
- `blocks`
- `InherentImplBlocks`
- `inherent_impl_blocks`
- `JSON`
- `XML`
- ... and 10 more

**Code:**

```simple
test "inherent_impl_blocks_22":
    trait JsonExt:
        fn to_json(self) -> String

    trait XmlExt:
        fn to_xml(self) -> String

    struct User:
        name: String
        age: i32

    impl JsonExt for User:
        fn to_json(self) -> String:
            return "{\"name\":\"" + self.name + "\"}"

    impl XmlExt for User:
        fn to_xml(self) -> String:
            return "<user><name>" + self.name + "</name></user>"

    # Different contexts can use different extensions
    use json::JsonExt
    let user = User(name: "Alice", age: 30)
    print(user.to_json())  # JSON output

    use xml::XmlExt
    print(user.to_xml())   # XML output
    assert_compiles()
```

### Test 23: Trait Coherence Rules {#trait_coherence_rules_23}

*Source line: ~9*

**Test name:** `trait_coherence_rules_23`

**Description:**

The orphan rule prevents defining trait implementations in "orphan" modules:

**Linked Symbols:**
- `coherence`
- `trait`
- `Trait`
- `trait_coherence_rules`
- `Rules`
- `Coherence`
- `TraitCoherenceRules`
- `rules`
- `MyType`
- `assert_compiles`
- ... and 9 more

**Code:**

```simple
test "trait_coherence_rules_23":
    # ALLOWED: Implementing your trait for any type
    # (trait is local)
    trait MyTrait:
        fn my_method()

    impl MyTrait for String:  # OK - MyTrait is local
        fn my_method():
            pass

    # ALLOWED: Implementing any trait for your type
    # (type is local)
    struct MyType:
        value: i32

    impl Display for MyType:  # OK - MyType is local
        fn fmt() -> str:
            return "{self.value}"

    # FORBIDDEN: Implementing foreign trait for foreign type
    impl Display for String:  # ERROR - both Display and String are foreign
        fn fmt() -> str:
            return self
    assert_compiles()
```

### Test 24: Trait Coherence Rules {#trait_coherence_rules_24}

*Source line: ~44*

**Test name:** `trait_coherence_rules_24`

**Description:**

Two trait implementations overlap if there exists a type that could match both:

**Linked Symbols:**
- `coherence`
- `trait`
- `Trait`
- `trait_coherence_rules`
- `Rules`
- `Coherence`
- `TraitCoherenceRules`
- `rules`
- `process`
- `Clone`
- ... and 5 more

**Code:**

```simple
test "trait_coherence_rules_24":
    # Overlapping implementations - ERROR
    trait Process:
        fn process()

    impl Process for i32:
        fn process():
            print("i32")

    impl[T: Clone] Process for T:  # ERROR: overlaps with impl for i32
        fn process():
            print("generic")
    assert_compiles()
```

### Test 25: Trait Coherence Rules {#trait_coherence_rules_25}

*Source line: ~64*

**Test name:** `trait_coherence_rules_25`

**Description:**

Specialization allows a more specific implementation to override a general one:

**Linked Symbols:**
- `coherence`
- `trait`
- `Trait`
- `trait_coherence_rules`
- `Rules`
- `Coherence`
- `TraitCoherenceRules`
- `rules`
- `process`
- `assert_compiles`
- ... and 3 more

**Code:**

```simple
test "trait_coherence_rules_25":
    # With specialization enabled
    trait Process:
        fn process()

    #[default]
    impl[T] Process for T:
        fn process():
            print("default")

    impl Process for i32:  # OK - specializes the default
        fn process():
            print("specialized for i32")
    assert_compiles()
```

### Test 26: Trait Coherence Rules {#trait_coherence_rules_26}

*Source line: ~85*

**Test name:** `trait_coherence_rules_26`

**Description:**

Blanket implementations apply to all types matching a bound:

**Linked Symbols:**
- `coherence`
- `trait`
- `Trait`
- `trait_coherence_rules`
- `Rules`
- `Coherence`
- `TraitCoherenceRules`
- `rules`
- `debug_fmt`
- `assert_compiles`
- ... and 5 more

**Code:**

```simple
test "trait_coherence_rules_26":
    # Blanket impl: all types implementing Debug also get Printable
    impl[T: Debug] Printable for T:
        fn stringify() -> String:
            return self.debug_fmt()
    assert_compiles()
```

### Test 27: Trait Coherence Rules {#trait_coherence_rules_27}

*Source line: ~98*

**Test name:** `trait_coherence_rules_27`

**Description:**

Associated types in trait implementations must be consistent:

**Linked Symbols:**
- `coherence`
- `trait`
- `Trait`
- `trait_coherence_rules`
- `Rules`
- `Coherence`
- `TraitCoherenceRules`
- `rules`
- `Container`
- `assert_compiles`
- ... and 7 more

**Code:**

```simple
test "trait_coherence_rules_27":
    trait Container:
        type Item

    # Each implementation fixes the associated type
    impl Container for IntList:
        type Item = i32

    impl Container for StringList:
        type Item = String

    # Cannot have multiple impls with different Item for same type
    impl Container for IntList:  # ERROR: conflicting impl
        type Item = i64
    assert_compiles()
```

### Test 28: Trait Coherence Rules {#trait_coherence_rules_28}

*Source line: ~118*

**Test name:** `trait_coherence_rules_28`

**Description:**

Negative bounds exclude types from a blanket impl:

**Linked Symbols:**
- `coherence`
- `trait`
- `Trait`
- `trait_coherence_rules`
- `Rules`
- `Coherence`
- `TraitCoherenceRules`
- `rules`
- `Clone`
- `assert_compiles`
- ... and 3 more

**Code:**

```simple
test "trait_coherence_rules_28":
    # Not yet implemented
    impl[T: !Copy] Clone for T:
        fn clone() -> T:
            # deep clone for non-Copy types
    assert_compiles()
```

### Test 29: Trait Coherence Rules {#trait_coherence_rules_29}

*Source line: ~161*

**Test name:** `trait_coherence_rules_29`

**Linked Symbols:**
- `coherence`
- `trait`
- `Trait`
- `trait_coherence_rules`
- `Rules`
- `Coherence`
- `TraitCoherenceRules`
- `rules`
- `ForeignTrait`
- `Now`
- ... and 4 more

**Code:**

```simple
test "trait_coherence_rules_29":
    # Wrap foreign type in local newtype
    struct MyString(String)

    impl ForeignTrait for MyString:
        # Now allowed - MyString is local
    assert_compiles()
```

### Test 30: Trait Coherence Rules {#trait_coherence_rules_30}

*Source line: ~170*

**Test name:** `trait_coherence_rules_30`

**Linked Symbols:**
- `coherence`
- `trait`
- `Trait`
- `trait_coherence_rules`
- `Rules`
- `Coherence`
- `TraitCoherenceRules`
- `rules`
- `Define`
- `assert_compiles`
- ... and 3 more

**Code:**

```simple
test "trait_coherence_rules_30":
    # Define local trait with desired methods
    trait StringExt:
        fn my_extension(self) -> String

    impl StringExt for String:
        fn my_extension(self) -> String:
            # implementation
    assert_compiles()
```

### Test 31: Trait Coherence Rules {#trait_coherence_rules_31}

*Source line: ~181*

**Test name:** `trait_coherence_rules_31`

**Linked Symbols:**
- `coherence`
- `trait`
- `Trait`
- `trait_coherence_rules`
- `Rules`
- `Coherence`
- `TraitCoherenceRules`
- `rules`
- `original_method`
- `assert_compiles`
- ... and 3 more

**Code:**

```simple
test "trait_coherence_rules_31":
    struct MyWrapper:
        inner: ForeignType

    impl MyWrapper:
        fn delegate_method(self):
            self.inner.original_method()
    assert_compiles()
```

### Test 32: Related Specifications {#related_specifications_32}

*Source line: ~16*

**Test name:** `related_specifications_32`

**Linked Symbols:**
- `Related`
- `specifications`
- `related_specifications`
- `related`
- `Specifications`
- `RelatedSpecifications`
- `Negative`
- `copy`
- `Clone`
- `assert_compiles`
- ... and 6 more

**Code:**

```simple
test "related_specifications_32":
    # Negative bound: T must NOT implement Clone
    impl[T: !Clone] Copy for T:
        fn copy() -> T:
            # implementation
            ...

    # Multiple bounds: T must be Send but NOT Sync
    impl[T: Send + !Sync] SafeWrapper for T:
        # implementation
        ...
    assert_compiles()
```

### Test 33: Related Specifications {#related_specifications_33}

*Source line: ~32*

**Test name:** `related_specifications_33`

**Description:**

1. Conditional Blanket Impls:

**Linked Symbols:**
- `Related`
- `specifications`
- `related_specifications`
- `related`
- `Specifications`
- `RelatedSpecifications`
- `types`
- `Clone`
- `deep_clone`
- `assert_compiles`
- ... and 5 more

**Code:**

```simple
test "related_specifications_33":
    # Default implementation for non-Copy types
    #[default]
    impl[T: !Copy] Clone for T:
        fn clone() -> T:
            return self.deep_clone()

    # Specialized for Copy types (more efficient)
    impl[T: Copy] Clone for T:
        fn clone() -> T:
            return self  # Simple copy
    assert_compiles()
```

### Test 34: Related Specifications {#related_specifications_34}

*Source line: ~46*

**Test name:** `related_specifications_34`

**Description:**

2. Avoiding Conflicts:

**Linked Symbols:**
- `Related`
- `specifications`
- `related_specifications`
- `related`
- `Specifications`
- `RelatedSpecifications`
- `For`
- `binary_serialize`
- `assert_compiles`
- `to_bytes`
- ... and 4 more

**Code:**

```simple
test "related_specifications_34":
    trait Serialize:
        fn to_bytes() -> [u8]

    # For types that don't have Display
    impl[T: !Display] Serialize for T:
        fn to_bytes() -> [u8]:
            return binary_serialize(self)

    # For types with Display (use text format)
    impl[T: Display] Serialize for T:
        fn to_bytes() -> [u8]:
            return self.to_string().as_bytes()
    assert_compiles()
```

### Test 35: Related Specifications {#related_specifications_35}

*Source line: ~62*

**Test name:** `related_specifications_35`

**Description:**

3. Marker Trait Exclusion:

**Linked Symbols:**
- `Related`
- `specifications`
- `related_specifications`
- `related`
- `Specifications`
- `RelatedSpecifications`
- `assert_compiles`
- `Only`
- `UnsafePointer`
- `NOT`
- ... and 1 more

**Code:**

```simple
test "related_specifications_35":
    trait UnsafePointer: ...

    # Only for types that are NOT UnsafePointer
    impl[T: !UnsafePointer] Safe for T:
        # Safe operations only
        ...
    assert_compiles()
```

### Test 36: Related Specifications {#related_specifications_36}

*Source line: ~81*

**Test name:** `related_specifications_36`

**Description:**

Example - Complete Pattern:

**Linked Symbols:**
- `Related`
- `specifications`
- `related_specifications`
- `related`
- `Specifications`
- `RelatedSpecifications`
- `process`
- `Clone`
- `assert_compiles`
- `Specific`
- ... and 3 more

**Code:**

```simple
test "related_specifications_36":
    trait Process:
        fn process()

    # Default for all types except Clone
    #[default]
    impl[T: !Clone] Process for T:
        fn process():
            print("processing non-cloneable")

    # Specific for Clone types
    impl[T: Clone] Process for T:
        fn process():
            print("processing cloneable")
    assert_compiles()
```

---

## Source Code

**View full specification:** [traits_spec.spl](../../tests/specs/traits_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/traits_spec.spl`*

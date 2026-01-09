# Simple Language Traits and Implementations - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/traits_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/traits_spec.spl
> ```

**Status:** ✅ Implemented (uses existing coherence rules)
**Feature IDs:** **Source:** traits.md
**Note:** This is a test extraction file. For complete specification text,

## Overview

This file contains executable test cases extracted from traits.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/traits.md

---

## Test Cases (36 total)

| Test | Section | Description |
|------|---------|-------------|
| [defining_a_trait_1](#test-1) | Defining a Trait |  |
| [defining_a_trait_2](#test-2) | Defining a Trait | The special `self` keyword in trait definitions refers to th... |
| [implementing_a_trait_3](#test-3) | Implementing a Trait | To implement a trait for a type, use an `impl Trait for Type... |
| [implementing_a_trait_4](#test-4) | Implementing a Trait | A type can implement any number of traits: |
| [unnamed_test](#test-5) | Dispatch | Traits support static dispatch by default - the compiler kno... |
| [dispatch_6](#test-6) | Dispatch | For cases where the concrete type isn't known at compile tim... |
| [unnamed_test](#test-7) | Trait Bounds and Generics | Traits are often used as bounds on type parameters: |
| [unnamed_test](#test-8) | Trait Bounds and Generics | This generic function `print_all` can accept a list of any t... |
| [unnamed_test](#test-9) | Trait Bounds and Generics | For complex bounds, use where clauses: |
| [trait_inheritance_10](#test-10) | Trait Inheritance | One trait can require another: |
| [associated_types_11](#test-11) | Associated Types | Traits can include associated type placeholders: |
| [trait_objects_and_collections_12](#test-12) | Trait Objects and Collections | Trait objects allow storing different types that implement t... |
| [common_standard_traits_13](#test-13) | Common Standard Traits | Common traits can be automatically derived: |
| [note_on_semantic_types_14](#test-14) | Note on Semantic Types | Trait methods in public APIs should follow the same semantic... |
| [interface_bindings_static_polymorphism_15](#test-15) | Interface Bindings (Static Polymorphism) | Important: The `bind` statement only supports static dispatc... |
| [interface_bindings_static_polymorphism_16](#test-16) | Interface Bindings (Static Polymorphism) | ```simple bind TraitName = ImplTypeName ``` |
| [collection_traits_17](#test-17) | Collection Traits | \| Type \| Iterable \| Collection \| Sequence \| MutSequence \| Im... |
| [inherent_impl_blocks_18](#test-18) | Inherent Impl Blocks | Methods can be added directly to types without using traits: |
| [inherent_impl_blocks_19](#test-19) | Inherent Impl Blocks | Extension methods allow adding methods to types defined else... |
| [inherent_impl_blocks_20](#test-20) | Inherent Impl Blocks |  |
| [inherent_impl_blocks_21](#test-21) | Inherent Impl Blocks | Example - Extending Standard Types: |
| [inherent_impl_blocks_22](#test-22) | Inherent Impl Blocks | Example - Multiple Extension Traits: |
| [trait_coherence_rules_23](#test-23) | Trait Coherence Rules | The orphan rule prevents defining trait implementations in "... |
| [trait_coherence_rules_24](#test-24) | Trait Coherence Rules | Two trait implementations overlap if there exists a type tha... |
| [trait_coherence_rules_25](#test-25) | Trait Coherence Rules | Specialization allows a more specific implementation to over... |
| [trait_coherence_rules_26](#test-26) | Trait Coherence Rules | Blanket implementations apply to all types matching a bound: |
| [trait_coherence_rules_27](#test-27) | Trait Coherence Rules | Associated types in trait implementations must be consistent... |
| [trait_coherence_rules_28](#test-28) | Trait Coherence Rules | Negative bounds exclude types from a blanket impl: |
| [trait_coherence_rules_29](#test-29) | Trait Coherence Rules |  |
| [trait_coherence_rules_30](#test-30) | Trait Coherence Rules |  |
| [trait_coherence_rules_31](#test-31) | Trait Coherence Rules |  |
| [related_specifications_32](#test-32) | Related Specifications |  |
| [related_specifications_33](#test-33) | Related Specifications | 1. Conditional Blanket Impls: |
| [related_specifications_34](#test-34) | Related Specifications | 2. Avoiding Conflicts: |
| [related_specifications_35](#test-35) | Related Specifications | 3. Marker Trait Exclusion: |
| [related_specifications_36](#test-36) | Related Specifications | Example - Complete Pattern: |

---

### Test 1: Defining a Trait

*Source line: ~3*

**Test name:** `defining_a_trait_1`

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

### Test 2: Defining a Trait

*Source line: ~19*

**Test name:** `defining_a_trait_2`

**Description:**

The special `self` keyword in trait definitions refers to the implementing instance type (like `Self...

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

### Test 3: Implementing a Trait

*Source line: ~5*

**Test name:** `implementing_a_trait_3`

**Description:**

To implement a trait for a type, use an `impl Trait for Type` block:

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

### Test 4: Implementing a Trait

*Source line: ~22*

**Test name:** `implementing_a_trait_4`

**Description:**

A type can implement any number of traits:

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

### Test 5: Dispatch

*Source line: ~7*

**Test name:** `unnamed_test`

**Description:**

Traits support static dispatch by default - the compiler knows at compile time the exact type and ca...

**Code:**

```simple
fn log[T: Printable](item: T):
    item.print_self()

let p = Person(name: "Alice", age: 30)
log(p)  # Compiler knows T = Person
```

### Test 6: Dispatch

*Source line: ~21*

**Test name:** `dispatch_6`

**Description:**

For cases where the concrete type isn't known at compile time, traits use dynamic dispatch by defaul...

**Code:**

```simple
test "dispatch_6":
    let x: Printable = somePrintableObject  # Uses vtable
    x.print_self()  # Dynamic dispatch
    assert_compiles()
```

### Test 7: Trait Bounds and Generics

*Source line: ~5*

**Test name:** `unnamed_test`

**Description:**

Traits are often used as bounds on type parameters:

**Code:**

```simple
fn print_all[T: Printable](items: List[T]):
    for item in items:
        item.print_self()
```

### Test 8: Trait Bounds and Generics

*Source line: ~15*

**Test name:** `unnamed_test`

**Description:**

This generic function `print_all` can accept a list of any type `T` that implements `Printable`. The...

**Code:**

```simple
fn process[T: Printable + Comparable](items: List[T]):
    for item in items:
        item.print_self()
    items.sort(\a, b: a.compare(b))
```

### Test 9: Trait Bounds and Generics

*Source line: ~28*

**Test name:** `unnamed_test`

**Description:**

For complex bounds, use where clauses:

**Code:**

```simple
fn complex[T, U](a: T, b: U) -> String
    where T: Printable,
          U: Comparable + Printable:
    return "{a.stringify()} vs {b.stringify()}"
```

### Test 10: Trait Inheritance

*Source line: ~5*

**Test name:** `trait_inheritance_10`

**Description:**

One trait can require another:

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

### Test 11: Associated Types

*Source line: ~5*

**Test name:** `associated_types_11`

**Description:**

Traits can include associated type placeholders:

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

### Test 12: Trait Objects and Collections

*Source line: ~5*

**Test name:** `trait_objects_and_collections_12`

**Description:**

Trait objects allow storing different types that implement the same trait:

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

### Test 13: Common Standard Traits

*Source line: ~18*

**Test name:** `common_standard_traits_13`

**Description:**

Common traits can be automatically derived:

**Code:**

```simple
test "common_standard_traits_13":
    #[derive(Eq, Hash, Clone, Debug)]
    struct Point:
        x: f64
        y: f64
    assert_compiles()
```

### Test 14: Note on Semantic Types

*Source line: ~5*

**Test name:** `note_on_semantic_types_14`

**Description:**

Trait methods in public APIs should follow the same semantic type guidelines as regular functions:

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

### Test 15: Interface Bindings (Static Polymorphism)

*Source line: ~9*

**Test name:** `interface_bindings_static_polymorphism_15`

**Description:**

Important: The `bind` statement only supports static dispatch. There is no `static` or `dyn` keyword...

**Code:**

```simple
test "interface_bindings_static_polymorphism_15":
    bind TraitName = ImplTypeName
    assert_compiles()
```

### Test 16: Interface Bindings (Static Polymorphism)

*Source line: ~15*

**Test name:** `interface_bindings_static_polymorphism_16`

**Description:**

```simple
bind TraitName = ImplTypeName
```

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

### Test 17: Collection Traits

*Source line: ~46*

**Test name:** `collection_traits_17`

**Description:**

| Type | Iterable | Collection | Sequence | MutSequence | ImmutSequence | Growable | Sliceable |
|--...

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

### Test 18: Inherent Impl Blocks

*Source line: ~5*

**Test name:** `inherent_impl_blocks_18`

**Description:**

Methods can be added directly to types without using traits:

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

### Test 19: Inherent Impl Blocks

*Source line: ~41*

**Test name:** `inherent_impl_blocks_19`

**Description:**

Extension methods allow adding methods to types defined elsewhere:

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

### Test 20: Inherent Impl Blocks

*Source line: ~62*

**Test name:** `inherent_impl_blocks_20`

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

### Test 21: Inherent Impl Blocks

*Source line: ~100*

**Test name:** `inherent_impl_blocks_21`

**Description:**

Example - Extending Standard Types:

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

### Test 22: Inherent Impl Blocks

*Source line: ~122*

**Test name:** `inherent_impl_blocks_22`

**Description:**

Example - Multiple Extension Traits:

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

### Test 23: Trait Coherence Rules

*Source line: ~9*

**Test name:** `trait_coherence_rules_23`

**Description:**

The orphan rule prevents defining trait implementations in "orphan" modules:

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

### Test 24: Trait Coherence Rules

*Source line: ~44*

**Test name:** `trait_coherence_rules_24`

**Description:**

Two trait implementations overlap if there exists a type that could match both:

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

### Test 25: Trait Coherence Rules

*Source line: ~64*

**Test name:** `trait_coherence_rules_25`

**Description:**

Specialization allows a more specific implementation to override a general one:

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

### Test 26: Trait Coherence Rules

*Source line: ~85*

**Test name:** `trait_coherence_rules_26`

**Description:**

Blanket implementations apply to all types matching a bound:

**Code:**

```simple
test "trait_coherence_rules_26":
    # Blanket impl: all types implementing Debug also get Printable
    impl[T: Debug] Printable for T:
        fn stringify() -> String:
            return self.debug_fmt()
    assert_compiles()
```

### Test 27: Trait Coherence Rules

*Source line: ~98*

**Test name:** `trait_coherence_rules_27`

**Description:**

Associated types in trait implementations must be consistent:

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

### Test 28: Trait Coherence Rules

*Source line: ~118*

**Test name:** `trait_coherence_rules_28`

**Description:**

Negative bounds exclude types from a blanket impl:

**Code:**

```simple
test "trait_coherence_rules_28":
    # Not yet implemented
    impl[T: !Copy] Clone for T:
        fn clone() -> T:
            # deep clone for non-Copy types
    assert_compiles()
```

### Test 29: Trait Coherence Rules

*Source line: ~161*

**Test name:** `trait_coherence_rules_29`

**Code:**

```simple
test "trait_coherence_rules_29":
    # Wrap foreign type in local newtype
    struct MyString(String)

    impl ForeignTrait for MyString:
        # Now allowed - MyString is local
    assert_compiles()
```

### Test 30: Trait Coherence Rules

*Source line: ~170*

**Test name:** `trait_coherence_rules_30`

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

### Test 31: Trait Coherence Rules

*Source line: ~181*

**Test name:** `trait_coherence_rules_31`

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

### Test 32: Related Specifications

*Source line: ~16*

**Test name:** `related_specifications_32`

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

### Test 33: Related Specifications

*Source line: ~32*

**Test name:** `related_specifications_33`

**Description:**

1. Conditional Blanket Impls:

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

### Test 34: Related Specifications

*Source line: ~46*

**Test name:** `related_specifications_34`

**Description:**

2. Avoiding Conflicts:

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

### Test 35: Related Specifications

*Source line: ~62*

**Test name:** `related_specifications_35`

**Description:**

3. Marker Trait Exclusion:

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

### Test 36: Related Specifications

*Source line: ~81*

**Test name:** `related_specifications_36`

**Description:**

Example - Complete Pattern:

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

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/traits_spec.spl`*

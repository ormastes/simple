# Simple Language Traits and Implementations

This document covers traits, trait implementations, trait bounds, and polymorphism.

## Overview

Traits in Simple are the mechanism for defining interfaces or abstract sets of methods that types can implement (similar to type classes in Haskell or interfaces in Java, but more flexible). A trait is a collection of method signatures (and optionally default method implementations) that describe some behavior.

Types (structs or classes) can implement these traits to guarantee they provide those methods, enabling polymorphic code that works over any type implementing the trait.

---

## Defining a Trait

```simple
trait Printable:
    fn stringify() -> String
    fn print_self():
        # default implementation
        print self.stringify()
```

Here, `Printable` is a trait with:
- One **required method** `stringify` (no default provided)
- One method `print_self` with a **default implementation**

The special `self` keyword in trait definitions refers to the implementing instance type (like `Self` in Rust traits).

### Trait with Multiple Methods

```simple
trait Comparable:
    fn compare(other: Self) -> i32
    fn equals(other: Self) -> bool:
        return self.compare(other) == 0
    fn less_than(other: Self) -> bool:
        return self.compare(other) < 0
    fn greater_than(other: Self) -> bool:
        return self.compare(other) > 0
```

Only `compare` is required; the other methods have defaults based on it.

---

## Implementing a Trait

To implement a trait for a type, use an `impl Trait for Type` block:

```simple
struct Person:
    name: String
    age: i32

impl Printable for Person:
    fn stringify() -> String:
        return "{self.name} (age {self.age})"
    # print_self uses the trait's default implementation
```

We provide an implementation for `stringify`. We did not provide `print_self`, so `Person` gets the default implementation from the trait automatically.

### Implementing Multiple Traits

A type can implement any number of traits:

```simple
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
```

---

## Dispatch

### Static Dispatch (Default)

Traits support static dispatch by default - the compiler knows at compile time the exact type and can optimize calls:

```simple
fn log[T: Printable](item: T):
    item.print_self()

let p = Person(name: "Alice", age: 30)
log(p)  # Compiler knows T = Person
```

Static dispatch uses monomorphization at compile time.

### Dynamic Dispatch

For cases where the concrete type isn't known at compile time, use trait objects:

```simple
let x: Printable = somePrintableObject  # Uses vtable
x.print_self()  # Dynamic dispatch
```

This is similar to `dyn Trait` in Rust.

---

## Trait Bounds and Generics

Traits are often used as bounds on type parameters:

```simple
fn print_all[T: Printable](items: List[T]):
    for item in items:
        item.print_self()
```

This generic function `print_all` can accept a list of any type `T` that implements `Printable`. The compiler enforces that only types implementing `Printable` are passed.

### Multiple Trait Bounds

```simple
fn process[T: Printable + Comparable](items: List[T]):
    for item in items:
        item.print_self()
    items.sort(\a, b: a.compare(b))
```

`T` must implement both `Printable` and `Comparable`.

### Where Clauses

For complex bounds, use where clauses:

```simple
fn complex[T, U](a: T, b: U) -> String
    where T: Printable,
          U: Comparable + Printable:
    return "{a.stringify()} vs {b.stringify()}"
```

---

## Trait Inheritance

One trait can require another:

```simple
trait Drawable: Printable:
    fn draw()

# Any Drawable must also be Printable
impl Drawable for Widget:
    fn stringify() -> String:
        return "Widget"
    fn draw():
        # drawing code
```

---

## Associated Types

Traits can include associated type placeholders:

```simple
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
```

---

## Trait Objects and Collections

Trait objects allow storing different types that implement the same trait:

```simple
let printables: [Printable] = [
    Person(name: "Alice", age: 30),
    Point(x: 1.0, y: 2.0),
    Widget("button"),
]

for p in printables:
    p.print_self()  # Dynamic dispatch
```

---

## Common Standard Traits

| Trait | Purpose | Key Method |
|-------|---------|------------|
| `Eq` | Equality comparison | `eq(other: &Self) -> bool` |
| `Ord` | Ordering comparison | `cmp(other: &Self) -> Ordering` |
| `Hash` | Hash computation | `hash() -> u64` |
| `Clone` | Deep copying | `clone() -> Self` |
| `Debug` | Debug representation | `debug_fmt() -> str` |
| `Display` | User-facing representation | `fmt() -> str` |
| `Default` | Default value | `default() -> Self` |
| `Iterator` | Iteration | `next() -> Option[Self::Item]` |

### Deriving Traits

Common traits can be automatically derived:

```simple
#[derive(Eq, Hash, Clone, Debug)]
struct Point:
    x: f64
    y: f64
```

---

## Polymorphism Summary

Simple supports polymorphism through:

1. **Traits** - Interface-like behavior without class inheritance
2. **Generics with bounds** - Compile-time polymorphism with type constraints
3. **Trait objects** - Runtime polymorphism via dynamic dispatch
4. **Multiple trait implementations** - A type can fulfill multiple interfaces

This encourages **composition over inheritance**: rather than subclassing a base class, implement traits that provide the desired behavior.

---

## Note on Semantic Types

Trait methods in public APIs should follow the same semantic type guidelines as regular functions:

```simple
# GOOD: Use semantic types in public trait methods
trait UserService:
    fn get_user(id: UserId) -> Option[User]
    fn set_status(id: UserId, status: UserStatus)

# Standard library traits use Option/Result
trait Iterator:
    type Item
    fn next(self) -> Option[Self.Item]
```

See [Unit Types](units.md) for the complete type safety policy.

---

## Interface Bindings (Static Polymorphism)

Interface bindings allow you to declare that a specific implementation type should be used for all instances of a trait type within a module. This enables **static dispatch** for trait method calls, eliminating vtable lookup overhead.

### Syntax

```simple
bind TraitName = ImplTypeName
```

### Example

```simple
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
```

### How It Works

1. **Compile-time**: The `bind` declaration is processed during parsing
2. **AST Rewriting**: The binding specializer rewrites method calls on bound trait types
3. **HIR/MIR Lowering**: Trait info includes vtable slot mappings for proper dispatch
4. **Interpreter**: Thread-local bindings enable static dispatch at runtime

### Benefits

- **Performance**: Eliminates vtable indirection for trait method calls
- **Inlining**: Enables the compiler to inline bound implementation methods
- **Deterministic Dispatch**: The exact implementation is known at compile time

### Scope Rules

- Bindings are module-local (scoped to the declaring module)
- Multiple modules can have different bindings for the same trait
- Bindings are resolved during compilation, not at runtime

### Use Cases

1. **Dependency Injection**: Bind interfaces to concrete implementations
2. **Testing**: Bind to mock implementations in test modules
3. **Performance-Critical Code**: Eliminate dynamic dispatch overhead
4. **Configuration**: Different builds can use different bindings

### Comparison with Dynamic Dispatch

| Aspect | `bind Interface = Impl` | `dyn Interface` |
|--------|------------------------|-----------------|
| Dispatch | Static (compile-time) | Dynamic (runtime) |
| Performance | No vtable overhead | Vtable lookup |
| Flexibility | Fixed at compile time | Can vary at runtime |
| Inlining | Possible | Not possible |

### Limitations

- Only one binding per trait per module
- Cannot change binding at runtime
- Binding must be to a concrete type that implements the trait

---

## Collection Traits

Simple provides a hierarchy of traits for collections that enable generic programming over `List`, `Array`, `Slice`, and `String`.

### Trait Hierarchy

```
Iterable[T]                    # Can produce iterator
    │
    ├── Collection[T]          # Has length, can check containment
    │       │
    │       ├── Sequence[T]    # Indexed access (read)
    │       │       │
    │       │       ├── MutSequence[T]     # Indexed write
    │       │       │
    │       │       └── ImmutSequence[T]   # Functional updates
    │       │
    │       └── Growable[T]    # Can add/remove (List only)
    │
    └── Sliceable[T]           # Can create slices
```

### Collection Trait Summary

| Trait | Purpose | Key Methods |
|-------|---------|-------------|
| `Iterable[T]` | Iteration support | `iter()`, `into_iter()` |
| `Collection[T]` | Sized container | `len()`, `is_empty()`, `contains()` |
| `Sequence[T]` | Indexed read | `get()`, `first()`, `last()`, `find()` |
| `MutSequence[T]` | Indexed write | `set()`, `swap()`, `sort()`, `reverse()` |
| `ImmutSequence[T]` | Functional ops | `with_index()`, `sorted()`, `filtered()`, `mapped()` |
| `Growable[T]` | Add/remove | `push()`, `pop()`, `insert()`, `remove()`, `clear()` |
| `Sliceable[T]` | Slice views | `as_slice()`, `as_mut_slice()` |

### Implementations

| Type | Iterable | Collection | Sequence | MutSequence | ImmutSequence | Growable | Sliceable |
|------|----------|------------|----------|-------------|---------------|----------|-----------|
| `List[T]` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| `Array[T, N]` | ✓ | ✓ | ✓ | ✓ | ✓ | ✗ | ✓ |
| `Slice[T]` | ✓ | ✓ | ✓ | ✗ | ✗ | ✗ | ✓ |
| `String` | ✓ | ✓ | ✓ | ✗ | ✓ | ✗ | ✓ |

### Generic Programming Example

```simple
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
```

See [Primitive as Object](primitive_as_obj.md) for full collection trait definitions.

---

## Inherent Impl Blocks

Methods can be added directly to types without using traits:

```simple
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
```

### Impl Block Features

| Feature | Description |
|---------|-------------|
| Instance methods | Take `self` as first parameter |
| Associated functions | No `self`, called via `Type.method()` |
| Constructors | Associated functions returning `Self` |
| Multiple impl blocks | A type can have multiple impl blocks |

### Extension Methods (Planned)

Extension methods allow adding methods to types defined elsewhere:

```simple
# In your module
impl String:
    fn to_title_case(self) -> String:
        # implementation
        ...

# Now all Strings have to_title_case()
let title = "hello world".to_title_case()  # "Hello World"
```

**Note:** Extension methods follow coherence rules - you can only extend types if either the type or the impl is in your crate.

---

### Extension Traits (#1154)

Extension traits provide a way to add methods to foreign types while following coherence rules. By defining a local trait, you can implement it for any type (foreign or local) since the trait is local.

**Pattern:**

```simple
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
```

**Coherence Rules:**

Extension traits follow the standard orphan rule:
- ✅ Local trait + Foreign type: **ALLOWED** (trait is local)
- ✅ Local trait + Local type: **ALLOWED** (both local)
- ❌ Foreign trait + Foreign type: **NOT ALLOWED** (neither local)

**Benefits:**

1. **Type Safety:** Methods are only available when trait is in scope
2. **No Conflicts:** Each crate defines its own extension traits
3. **Explicit:** `use my_extensions::StringExt` makes it clear
4. **Testable:** Can mock implementations for testing

**Example - Extending Standard Types:**

```simple
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
```

**Example - Multiple Extension Traits:**

```simple
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
```

**Coherence Validation:**

The coherence checker automatically enforces extension trait rules:
- Extension trait implementations must have local trait
- No special syntax or attributes needed
- Works with all existing coherence features (specialization, etc.)

**Status:** ✅ Implemented (uses existing coherence rules)

## Trait Coherence Rules

Coherence ensures that trait implementations are unambiguous and predictable across the entire program. Without coherence rules, different parts of a program could define conflicting implementations.

### The Orphan Rule

The **orphan rule** prevents defining trait implementations in "orphan" modules:

```simple
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
```

**The Orphan Rule (Formal):**

An `impl Trait for Type` is allowed only if:
- `Trait` is defined in the current crate, OR
- `Type` is defined in the current crate

### Overlap and Ambiguity

Two trait implementations **overlap** if there exists a type that could match both:

```simple
# Overlapping implementations - ERROR
trait Process:
    fn process()

impl Process for i32:
    fn process():
        print("i32")

impl[T: Clone] Process for T:  # ERROR: overlaps with impl for i32
    fn process():
        print("generic")
```

**Resolution:** The compiler rejects overlapping implementations. Use more specific bounds or separate traits.

### Specialization (Planned)

Specialization allows a more specific implementation to override a general one:

```simple
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
```

**Note:** Specialization is planned but not yet implemented. Currently, all overlaps are errors.

### Blanket Implementations

Blanket implementations apply to all types matching a bound:

```simple
# Blanket impl: all types implementing Debug also get Printable
impl[T: Debug] Printable for T:
    fn stringify() -> String:
        return self.debug_fmt()
```

**Coherence interaction:** Blanket implementations can create overlap issues. The orphan rule still applies.

### Associated Type Coherence

Associated types in trait implementations must be consistent:

```simple
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
```

### Negative Trait Bounds (Planned)

Negative bounds exclude types from a blanket impl:

```simple
# Not yet implemented
impl[T: !Copy] Clone for T:
    fn clone() -> T:
        # deep clone for non-Copy types
```

### Coherence Error Messages

```
error[E0119]: conflicting implementations of trait `Display` for type `String`
  --> src/my_impl.spl:5:1
   |
 5 | impl Display for String:
   | ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: conflicting implementation in `std`
   = help: consider defining a newtype wrapper

error[E0117]: only traits defined in the current crate can be implemented for arbitrary types
  --> src/orphan.spl:3:1
   |
 3 | impl Debug for Vec[i32]:
   | ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `Debug` is defined in `std`, not the current crate
   = note: `Vec` is defined in `std`, not the current crate
   = help: wrap `Vec[i32]` in a newtype: `struct MyVec(Vec[i32])`
```

### Coherence Summary

| Rule | Purpose | Error Code |
|------|---------|------------|
| **Orphan rule** | Prevent external conflicts | E0117 |
| **No overlap** | Unambiguous dispatch | E0119 |
| **Consistent associated types** | Type safety | E0120 |

### Workarounds for Coherence Restrictions

When coherence rules prevent desired implementations:

**1. Newtype Pattern:**
```simple
# Wrap foreign type in local newtype
struct MyString(String)

impl ForeignTrait for MyString:
    # Now allowed - MyString is local
```

**2. Extension Traits:**
```simple
# Define local trait with desired methods
trait StringExt:
    fn my_extension(self) -> String

impl StringExt for String:
    fn my_extension(self) -> String:
        # implementation
```

**3. Delegation:**
```simple
struct MyWrapper:
    inner: ForeignType

impl MyWrapper:
    fn delegate_method(self):
        self.inner.original_method()
```

---

## Related Specifications

- [Data Structures](data_structures.md)
- [Functions](functions.md)
- [Types](types.md)
- [Unit Types](units.md)
- [Primitive as Object](primitive_as_obj.md)
- [Design TODOs](../design/type_system_features.md)

### Negative Trait Bounds (#1151)

Negative trait bounds allow excluding types that implement certain traits. This is useful for conditional implementations and avoiding conflicts.

**Syntax:**

```simple
# Negative bound: T must NOT implement Clone
impl[T: !Clone] Copy for T:
    fn copy() -> T:
        # implementation
        ...

# Multiple bounds: T must be Send but NOT Sync
impl[T: Send + !Sync] SafeWrapper for T:
    # implementation
    ...
```

**Use Cases:**

1. **Conditional Blanket Impls:**
```simple
# Default implementation for non-Copy types
#[default]
impl[T: !Copy] Clone for T:
    fn clone() -> T:
        return self.deep_clone()

# Specialized for Copy types (more efficient)
impl[T: Copy] Clone for T:
    fn clone() -> T:
        return self  # Simple copy
```

2. **Avoiding Conflicts:**
```simple
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
```

3. **Marker Trait Exclusion:**
```simple
trait UnsafePointer: ...

# Only for types that are NOT UnsafePointer
impl[T: !UnsafePointer] Safe for T:
    # Safe operations only
    ...
```

**Coherence Rules:**

Negative bounds interact with specialization and overlap detection:

- Two impls can coexist if one has negative bound: `T: Clone` vs `T: !Clone`
- Negative bounds create disjoint sets (no overlap possible)
- Specialization with #[default] still needed for same bounds

**Example - Complete Pattern:**

```simple
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
```

**Status:** 🔄 Partial
- AST support: ✅ Complete (`negative_bounds` field in `WhereBound`)
- Parser support: 📋 Planned (`!Trait` syntax parsing)
- Coherence checking: ✅ Infrastructure ready
- Type checking: 📋 Planned (enforce exclusion at compile time)

**Note:** Currently, the AST supports negative bounds but parser and full validation are pending. The coherence checker has infrastructure ready for when parser support is added.


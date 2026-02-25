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

## Related Specifications

- [Data Structures](data_structures.md)
- [Functions](functions.md)
- [Types](types.md)
- [Unit Types](units.md)
- [Primitive as Object](primitive_as_obj.md)
- [Design TODOs](../design/type_system_features.md)

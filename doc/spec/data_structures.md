# Simple Language Data Structures

This document covers structs, classes, enums, unions, and their associated features.

## Structs and Classes Overview

Structs and classes are the two mechanisms for defining custom composite types in Simple, each with distinct semantics.

---

## Structs (Value Types)

Structs are value types (similar to structs in C or Rust). They are copied on assignment and passed by value (the compiler may optimize large structs by reference under the hood). Structs are ideal for small, immutable data groupings like points, ranges, or data transfer objects.

### Basic Struct

```simple
struct Point:
    x: f64
    y: f64

a = Point(x: 1, y: 2)
b = a              # copies the values x=1, y=2 into b
# a.x = 5          # Error: Point is immutable by default
```

### Mutable Structs

Unless marked `mut`, a struct's fields cannot be changed after construction:

```simple
mut struct Cursor:
    x: f64
    y: f64

let c = Cursor(x: 0, y: 0)
c.x = 10           # OK: Cursor is mutable
```

### Struct Characteristics

- **Immutable by default** - Use `mut struct` for mutable structs
- **Value equality** - Two Points with same x,y are equal
- **No inheritance** - Structs cannot subclass other structs
- **Can implement traits** - Polymorphism via trait implementations
- **Copied on assignment** - Each variable has its own copy

---

## Classes (Reference Types)

Classes are reference types, allocated on the heap and managed by the runtime (with garbage collection). Variables of class type are references (pointers) to objects.

### Basic Class

```simple
class Person:
    name: String
    age: i32

    fn birthday():
        self.age = self.age + 1

let p = Person(name: "Alice", age: 30)
p.birthday()          # now age is 31
```

### Immutable Classes

By default, class instances are mutable. Use `immut` for immutable classes:

```simple
immut class Color:
    red: u8
    green: u8
    blue: u8

# Fields cannot be changed after construction
```

### Class Characteristics

- **Mutable by default** - Use `immut class` for immutable classes
- **Reference equality by default** - Override `.equals` for structural equality
- **Single inheritance** - A class may inherit from one base class
- **Can implement traits** - Multiple traits can be implemented
- **Reference semantics** - Assignment shares the same object

### Reference Semantics

```simple
let p = Person(name: "Alice", age: 30)
let q = p              # q and p refer to the same object
q.age = 31             # p.age is also 31
```

---

## Auto-Forwarding Properties (get/set/is)

Simple provides automatic property forwarding for methods prefixed with `get_`, `set_`, or `is_`. This enables encapsulation with minimal boilerplate.

### Basic Syntax

```simple
class Person:
    # These methods auto-create private backing field '_name'
    fn get_name() -> str:
        return _name

    fn set_name(value: str):
        _name = value

    # 'is_' prefix for boolean properties
    fn is_active() -> bool:
        return _active

let p = Person()
p.set_name("Alice")      # Sets _name
print p.get_name()       # Gets _name -> "Alice"
```

### Auto-Generated Backing Fields

| Method | Backing Field | Type |
|--------|---------------|------|
| `get_name() -> str` | `_name: str` | Inferred from return type |
| `set_name(v: str)` | `_name: str` | Inferred from parameter type |
| `is_valid() -> bool` | `_valid: bool` | Always `bool` |

### Read-Only Properties

If only `get_` is defined, the property is read-only from outside:

```simple
class Counter:
    fn get_count() -> i64:
        return _count

    fn increment():
        _count = _count + 1  # Internal modification OK

let c = Counter()
c.increment()
print c.get_count()  # OK: 1
# c.set_count(100)   # Error: no setter defined
```

### Write-Only Properties

If only `set_` is defined, the property is write-only from outside:

```simple
class SecureData:
    fn set_password(value: str):
        _password = hash(value)

    fn verify(input: str) -> bool:
        return hash(input) == _password

let s = SecureData()
s.set_password("secret123")
# print s.get_password()  # Error: no getter defined
```

### Default Values

| Type | Default |
|------|---------|
| Numeric (i32, f64, etc.) | `0` |
| `bool` | `false` |
| `str` | `""` |
| Reference types | `nil` |

---

## Enums (Algebraic Data Types)

Enums define a type that can be one of several variants, each possibly carrying data. They are algebraic data types, similar to those in Rust or Haskell.

### Defining an Enum

```simple
enum Result[T]:
    Ok(value: T)
    Err(error: String)
```

This defines a generic enum with two variants: `Ok` holding a value of type `T`, and `Err` holding an error message.

### Using Enums

Enums are typically used with pattern matching:

```simple
fn handle(result: Result[i64]):
    match result:
        case Ok(val):
            print "Success: {val}"
        case Err(msg):
            print "Error: {msg}"
```

### Enum Characteristics

- **Value types** - Like structs, copied on assignment
- **Immutable by default** - Contents can't be changed after creation
- **Can be parameterized** - Generic enums like `Result[T]`
- **Pattern matching** - Safe, exhaustive branching on variants

---

## Strong Enums

The `#[strong]` attribute enforces **exhaustive explicit matching**, disallowing wildcard `_` patterns.

### Basic Strong Enum

```simple
#[strong]
enum HttpStatus:
    Ok
    NotFound
    ServerError
    BadRequest
    Unauthorized

fn handle_status(status: HttpStatus) -> str:
    match status:
        case Ok: "Success"
        case NotFound: "Not found"
        case ServerError: "Server error"
        case BadRequest: "Bad request"
        case Unauthorized: "Unauthorized"
        # No _ allowed - all cases must be explicit
```

### Why Strong Enums?

Strong enums prevent bugs when new variants are added:

```simple
# Without #[strong] - wildcard hides missing cases
enum Status:
    Active
    Inactive
    Pending      # Added later

fn process(s: Status):
    match s:
        case Active: activate()
        case Inactive: deactivate()
        case _: pass     # Silently ignores Pending - BUG!

# With #[strong] - compiler catches missing cases
#[strong]
enum Status:
    Active
    Inactive
    Pending

fn process(s: Status):
    match s:
        case Active: activate()
        case Inactive: deactivate()
        # ERROR: missing case 'Pending', wildcards not allowed
```

### Strong Enum Use Cases

| Use Case | Example |
|----------|---------|
| State machines | `#[strong] enum State: Idle, Running, Paused, Stopped` |
| HTTP status | `#[strong] enum HttpStatus: Ok, NotFound, ServerError` |
| Error types | `#[strong] enum Error: Io, Parse, Network, Auth` |
| Commands | `#[strong] enum Command: Start, Stop, Restart, Status` |

### Opt-Out for Specific Matches

Use `#[allow(wildcard_match)]` to allow wildcards in specific functions:

```simple
#[allow(wildcard_match)]
fn handle_some(e: Event):
    match e:
        case Click: on_click()
        case _: pass     # OK with attribute
```

---

## Union Types

Simple supports union types for cases where a variable might hold one of multiple types.

### Anonymous Union Types

```simple
fn example(x: i64 | str):
    match x:
        case i: i64:
            print "Integer: {i}"
        case s: String:
            print "String: {s}"
```

The notation `i64 | str` treats this as an anonymous union of two types. Under the hood, this compiles into an enum with two variants.

### Tagged vs Untagged Unions

| Type | Description | Safety |
|------|-------------|--------|
| Tagged unions (enums) | Each variant has implicit tag | Safe - must match tag to access |
| Untagged unions | Same memory, different types | Unsafe - not supported in Simple |

Simple only supports tagged unions (enums) to maintain type safety.

---

## Option Type

A common enum representing "something or nothing":

```simple
enum Option[T]:
    Some(value: T)
    None

fn find(id: UserId) -> Option[User]:
    match lookup(id):
        case found:
            return Some(found)
        case _:
            return None
```

**Important:** Simple requires explicit `Option[T]` for nullable values. Implicit `nil` is a compile error:

```simple
# ERROR: Implicit nullable return
fn find_user(id: UserId) -> User:  # Compile error if function can return nil
    ...

# CORRECT: Explicit Option
fn find_user(id: UserId) -> Option[User]:
    ...
```

This is used instead of null values to represent the absence of a value in a type-safe way. See [Unit Types](units.md) for more on the type safety policy.

---

## Visibility and Access

By default, all struct and class fields are publicly readable but only modifiable according to mutability rules. Access modifiers can restrict access:

```simple
class User:
    pub id: UserId           # Public field - uses semantic type
    pub name: str            # OK: str is allowed in public APIs
    pub status: UserStatus   # Uses enum instead of bool
    private password: str    # Private field

    fn verify(input: str) -> bool:   # OK: bool in private method
        return hash(input) == self.password
```

---

## Related Specifications

- [Types and Mutability](types.md)
- [Unit Types](units.md)
- [Functions and Pattern Matching](functions.md)
- [Memory and Ownership](memory.md)
- [Traits](traits.md)

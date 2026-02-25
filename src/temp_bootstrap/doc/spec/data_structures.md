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

### Impl Blocks for Enums

Enums can have methods added via impl blocks:

```simple
enum Shape:
    Circle(radius: f64)
    Rectangle(width: f64, height: f64)

impl Shape:
    fn area(self) -> f64:
        match self:
            case Circle(r): return 3.14159 * r * r
            case Rectangle(w, h): return w * h

    fn scale(self, factor: f64) -> Shape:
        match self:
            case Circle(r): return Shape.Circle(radius: r * factor)
            case Rectangle(w, h): return Shape.Rectangle(width: w * factor, height: h * factor)

    # Associated function (no self)
    fn unit_circle() -> Shape:
        return Shape.Circle(radius: 1.0)

# Usage
let s = Shape.Circle(radius: 5.0)
print s.area()           # 78.54
let s2 = s.scale(2.0)    # Circle with radius 10.0
```

### Trait Implementations for Enums

```simple
trait Drawable:
    fn draw(self)

impl Drawable for Shape:
    fn draw(self):
        match self:
            case Circle(r): draw_circle(r)
            case Rectangle(w, h): draw_rect(w, h)

# Common traits can be derived
#[derive(Eq, Clone, Debug)]
enum Color:
    Red
    Green
    Blue
```

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

## Result Type

A common enum representing "success or error":

```simple
enum Result[T, E]:
    Ok(value: T)
    Err(error: E)

fn parse_int(s: str) -> Result[i64, ParseError]:
    if s.is_numeric():
        return Ok(s.to_int())
    return Err(ParseError(msg: "Invalid number: {s}"))
```

### Error Propagation Operator (`?`)

The `?` operator propagates errors automatically:

```simple
fn read_config() -> Result[Config, IoError]:
    let content = read_file("config.toml")?  # Returns early if Err
    let parsed = parse_toml(content)?        # Returns early if Err
    return Ok(Config(parsed))

# Equivalent to:
fn read_config_verbose() -> Result[Config, IoError]:
    match read_file("config.toml"):
        case Ok(content):
            match parse_toml(content):
                case Ok(parsed): return Ok(Config(parsed))
                case Err(e): return Err(e)
        case Err(e): return Err(e)
```

### Result Methods

```simple
impl Result[T, E]:
    fn is_ok() -> bool
    fn is_err() -> bool
    fn unwrap() -> T                    # Panics if Err
    fn unwrap_or(default: T) -> T
    fn unwrap_err() -> E                # Panics if Ok
    fn map[U](f: fn(T) -> U) -> Result[U, E]
    fn map_err[F](f: fn(E) -> F) -> Result[T, F]
    fn and_then[U](f: fn(T) -> Result[U, E]) -> Result[U, E]
```

### Shorthand Syntax

```simple
# These are equivalent:
fn foo() -> Result[i64, Error]
fn foo() -> i64 | Error
```

---

## Bitfields

Bitfields allow compact representation of data at the bit level, useful for hardware registers, protocol headers, and flags.

### Defining a Bitfield

```simple
bitfield Flags(u8):
    readable: 1      # bit 0
    writable: 1      # bit 1
    executable: 1    # bit 2
    _reserved: 5     # bits 3-7 (padding, not accessible)
```

The backing type (`u8`, `u16`, `u32`, `u64`) determines the total size.

### Using Bitfields

```simple
let f = Flags(readable: 1, writable: 1, executable: 0)
print f.readable     # 1
f.writable = 0       # Clear write bit
let raw = f.raw()    # Get underlying u8 value: 0b00000001
```

### Multi-Bit Fields

Fields can span multiple bits:

```simple
bitfield Color(u32):
    red: 8           # bits 0-7
    green: 8         # bits 8-15
    blue: 8          # bits 16-23
    alpha: 8         # bits 24-31

let c = Color(red: 255, green: 128, blue: 64, alpha: 255)
```

### Bitfield Characteristics

| Property | Description |
|----------|-------------|
| Packed | Fields are tightly packed with no padding between them |
| Little-endian | Fields fill from LSB to MSB |
| Value type | Copied on assignment like structs |
| FFI-safe | Compatible with C bitfields |

### Named Constants

```simple
bitfield Permission(u8):
    read: 1
    write: 1
    execute: 1

    const READ_ONLY = Permission(read: 1, write: 0, execute: 0)
    const READ_WRITE = Permission(read: 1, write: 1, execute: 0)
    const FULL = Permission(read: 1, write: 1, execute: 1)
```

---

## Related Specifications

- [Types and Mutability](types.md)
- [Unit Types](units.md)
- [Functions and Pattern Matching](functions.md)
- [Memory and Ownership](memory.md)
- [Traits](traits.md)
- [Design TODOs](../design/type_system_features.md)

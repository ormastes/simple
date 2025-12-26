# Simple Language Type System

This document covers the type system, mutability rules, unit types, and type inference.

## Type System Overview

Simple is statically typed, but it features type inference to reduce verbosity. The compiler can often deduce the types of variables and expressions from context, so developers do not need to annotate types everywhere. For example, `let count = 5` automatically infers `count` to be an `i64`. However, you can explicitly annotate types when needed for clarity or interface definitions (e.g. `let count: i64 = 5`). Every value and expression has a definite type at compile time, even if not explicitly written, due to inference.

---

## Built-in Types

### Primitive Types

| Category | Types | Description |
|----------|-------|-------------|
| Signed integers | `i8`, `i16`, `i32`, `i64` | 8/16/32/64-bit signed integers |
| Unsigned integers | `u8`, `u16`, `u32`, `u64` | 8/16/32/64-bit unsigned integers |
| Floating point | `f32`, `f64` | 32/64-bit IEEE 754 floats |
| Boolean | `bool` | `true` or `false` |
| Text | `str` | UTF-8 string type |
| Null | `nil` | Absence of value |

### Compound Types

| Type | Syntax | Object Type | Description |
|------|--------|-------------|-------------|
| Tuples | `(T1, T2, ...)` | `Tuple` | Fixed-size heterogeneous collections |
| Lists | `[T]` | `List[T]` | Dynamic-size homogeneous collections |
| Fixed arrays | `[T; N]` | `Array[T, N]` | Fixed-size homogeneous collections |
| Dictionaries | `{Key: Value}` | `Map[K, V]` | Key-value mappings |
| Functions | `fn(T1, T2) -> R` | `Fn[Args, R]` | Function types |
| Generics | `List[T]` | - | Parameterized types |

**Note:** Primitive syntax like `[]` and `[T; N]` is promoted to full object types. See [Primitive as Object](primitive_as_obj.md) for details.

---

## Mutability Rules

Simple enforces clear mutability rules for data structures to encourage safe programming. Immutability is the default for value types, aligning with modern best practices.

### Structs (Value Types)

Structs are **immutable by default**. Fields cannot be modified after construction unless marked `mut`:

```simple
struct Point:
    x: f64
    y: f64

mut struct Cursor:
    x: f64
    y: f64
```

`Point` is immutable (once created, you can't change its `x` or `y`), whereas `Cursor` is mutable. Making immutability the default encourages asking "does this really need to be mutable?" which leads to safer designs.

### Classes (Reference Types)

Classes are **mutable by default**. They represent objects on the heap that are referred to by reference:

```simple
class Person:
    name: String
    age: i32

immut class Color:
    red: u8
    green: u8
    blue: u8
```

`Person` is mutable (you can change name or age), while `Color` is immutable. An `immut` class requires that all its fields are either immutable types or also marked immutable.

### Variables

Variables in Simple are **mutable by default** (like Python) for ease of use. The `let` keyword is optional. Use `const` for immutable bindings:

```simple
x = 10            # mutable variable (let is optional)
let y = 20        # also mutable (let is explicit but optional)
x = 30            # ok, x is mutable
y = 40            # ok, y is mutable

const MAX = 100   # immutable constant
MAX = 200         # compile error, const cannot be reassigned
```

### Mutability Summary

| Declaration | Mutable by Default? | Make Immutable | Make Mutable |
|-------------|---------------------|----------------|--------------|
| `struct` | No | (default) | `mut struct` |
| `class` | Yes | `immut class` | (default) |
| Variables | Yes | `const` | (default) |

---

## Unit Types and Literal Suffixes

Simple provides **unit types** for type-safe numeric values with physical dimensions or semantic meaning.

### Basic Unit Families

A **unit family** defines related units with a common base type and automatic conversions:

```simple
# Syntax: unit name(base: BaseType): suffix = factor, ...
unit length(base: f64):
    mm = 0.001        # 1 mm = 0.001 meters
    cm = 0.01         # 1 cm = 0.01 meters
    m = 1.0           # base unit
    km = 1000.0       # 1 km = 1000 meters
    inch = 0.0254
    ft = 0.3048
    mile = 1609.34

unit time(base: f64):
    ns = 0.000000001
    us = 0.000001
    ms = 0.001
    s = 1.0           # base unit
    min = 60.0
    hr = 3600.0

unit mass(base: f64):
    mg = 0.000001
    g = 0.001
    kg = 1.0          # base unit
    lb = 0.453592
```

### Using Unit Literals

Values are created using the `_suffix` notation:

```simple
let distance = 100_km         # length type, stored as 100000.0 (meters)
let duration = 2_hr           # time type, stored as 7200.0 (seconds)
let weight = 5_kg             # mass type, stored as 5.0 (kg)

# Access value in specific unit
distance.as_km()              # 100.0
distance.as_m()               # 100000.0
distance.as_mile()            # 62.137...

# Operations within same family (auto-converts)
let total = 1_km + 500_m      # 1500_m (stored as 1500.0)

# Comparisons work across units
1_km == 1000_m                # true
```

### Composite Unit Types

**Composite units** are derived from operations between unit families:

```simple
unit velocity(base: f64) = length / time:
    mps = 1.0         # meters per second (base)
    kmph = 0.277778   # km/hr in m/s
    mph = 0.44704     # miles/hr in m/s

unit area(base: f64) = length * length:
    sqmm = 0.000001
    sqcm = 0.0001
    sqm = 1.0         # base
    sqkm = 1000000.0

unit force(base: f64) = mass * acceleration:
    N = 1.0           # Newton (base)
    kN = 1000.0
```

### Composite Type Inference

The compiler infers result types from composite definitions:

```simple
let distance = 100_km
let duration = 2_hr

# Compiler infers: length / time = velocity
let speed = distance / duration    # velocity type, 50_kmph

# Compiler infers: velocity * time = length
let new_dist = speed * 3_hr        # length type, 150_km
```

### Standalone Unit Types

For semantic types without physical dimensions:

```simple
# Syntax: unit Name: BaseType as suffix [= factor]
unit UserId: i64 as uid
unit Percentage: f64 as pct = 0.01        # 50_pct = 0.5 internally
unit Celsius: f64 as c
unit Fahrenheit: f64 as f

# Usage
let user = 42_uid
let discount = 20_pct                      # stored as 0.2
let temp = 25_c
```

### Type Safety

Unit types prevent mixing incompatible values:

```simple
let distance = 100_km
let duration = 2_hr

# ERROR: different unit families
let bad = distance + duration    # Compile error: length + time

# OK: same family
let ok = 1_km + 500_m            # OK: both length
```

### Unit Type Summary

| Declaration | Purpose | Example |
|-------------|---------|---------|
| `unit name(base: T): ...` | Unit family | `unit length(base: f64): m = 1.0, km = 1000.0` |
| `unit name(base: T) = A op B: ...` | Composite unit | `unit velocity(base: f64) = length / time: mps = 1.0` |
| `unit Name: T as suffix` | Standalone unit | `unit UserId: i64 as uid` |

---

## Primitive Type Warnings (Public APIs)

Simple **warns** when bare primitives are used in public APIs. Use semantic types (unit types, enums, Option) instead for better type safety and self-documenting code.

### Warning Rules

**WARNING** when used in public functions, methods, and fields:
- Bare numeric types: `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`, `f32`, `f64`
- Bare `bool` - use enums for semantic meaning

**ERROR** (always, cannot be suppressed):
- Implicit `nil` - must use `Option[T]` explicitly

**NO WARNING**:
- `str` - text is inherently string
- Unit types (e.g., `UserId`, `Meters`, `Seconds`)
- Enums for states and flags (instead of `bool`)
- `Option[T]` for nullable values
- `Result[T, E]` for fallible operations

### Examples

```simple
# WARNING: Bare primitives in public API
pub fn get_user_id() -> i64:           # Warning: use unit type
    return 42

pub fn set_active(active: bool):       # Warning: use enum
    ...

pub class User:
    pub id: i64                        # Warning: use unit type
    pub age: i32                       # Warning: use unit type

# RECOMMENDED: Use semantic types (no warnings)
unit UserId: i64 as uid
unit Age: i32 as age

enum UserStatus:
    Active
    Inactive
    Suspended

pub fn get_user_id() -> UserId:        # OK - no warning
    return 42_uid

pub fn set_status(status: UserStatus): # OK - no warning
    ...

pub class User:
    pub id: UserId                     # OK
    pub name: str                      # OK (str is allowed)
    pub age: Age                       # OK
    pub status: UserStatus             # OK
```

### Semantic Boolean Replacement

Instead of `bool`, use descriptive enums:

```simple
# WARNING: What does true/false mean?
pub fn configure(enabled: bool, visible: bool):  # Warning
    ...

# GOOD: Clear meaning (no warning)
enum Enabled:
    Yes
    No

enum Visibility:
    Visible
    Hidden

pub fn configure(enabled: Enabled, visibility: Visibility):  # OK
    ...

# Call site is now self-documenting
configure(Enabled.Yes, Visibility.Hidden)
```

### Option for Nullable Values

```simple
# ERROR: Implicit nullable return (always an error)
pub fn find_user(id: UserId) -> User:  # Compile ERROR if can return nil
    ...

# CORRECT: Explicit Option
pub fn find_user(id: UserId) -> Option[User]:
    match lookup(id):
        case found: Some(found)
        case _: None
```

**Note:** Unlike `primitive_api` which is a warning, implicit `nil` is always a compile error. Simple does not allow nullable types without explicit `Option[T]`.

### Private Code Exception

Private/internal code MAY use bare primitives without warnings:

```simple
# OK: private function - no warning
fn internal_calc(a: i64, b: i64) -> i64:
    return a + b

# Public wrapper uses semantic types
pub fn calculate_total(price: Price, quantity: Quantity) -> Total:
    let raw = internal_calc(price.raw(), quantity.raw())
    return Total.from_raw(raw)
```

### Warning Control Attributes

```simple
# Directory-level (in __init__.spl)
#[deny(primitive_api)]
mod my_strict_module

# Item-level - suppress warning
#[allow(primitive_api)]
pub fn read_raw_bytes(count: i32) -> [u8]:
    ...

# Item-level - treat as error
#[deny(primitive_api)]
pub fn strict_function(id: i64):  # Now a compile ERROR
    ...
```

Lint attributes in `__init__.spl` inherit to all files and child directories.

### Project-Level Warning Control

In `simple.toml`, configure warning behavior:

```toml
[lint]
primitive_api = "warn"    # Default: emit warning
# primitive_api = "deny"  # Treat as error
# primitive_api = "allow" # Suppress entirely
```

### Standard Library Policy

The standard library uses `#[deny(primitive_api)]` in its root `__init__.spl`:

```simple
# std/__init__.spl
#[deny(primitive_api)]
mod std

pub mod core
pub mod collections
# ... all child modules inherit the deny setting
```

This means:
- User code: warnings by default (can upgrade to errors)
- Standard library: errors via `__init__.spl` inheritance (no bare primitives allowed)

### Type Rules Summary

| Type | Public API | Private Code |
|------|------------|--------------|
| `i8`-`i64`, `u8`-`u64` | ⚠️ WARNING | ✓ OK |
| `f32`, `f64` | ⚠️ WARNING | ✓ OK |
| `bool` | ⚠️ WARNING | ✓ OK |
| `nil` (implicit) | ❌ ERROR | ❌ ERROR |
| `str` | ✓ OK | ✓ OK |
| Unit types | ✓ OK | ✓ OK |
| Enums | ✓ OK | ✓ OK |
| `Option[T]` | ✓ OK | ✓ OK |
| `Result[T, E]` | ✓ OK | ✓ OK |

**Note:** Implicit `nil` is always an error everywhere - this is a language safety rule, not a lint.

---

## Type Inference

Type inference works in tandem with mutability rules:

```simple
# Type inferred as Point (immutable)
let p = Point(3, 4)
# p.x = 5          # Error: Point is immutable

# Type inferred as Cursor (mutable)
let cur = Cursor(0, 0)
cur.x = 5           # OK: Cursor is mutable
```

### Unit Type Inference

The compiler maintains a **unit algebra** based on composite definitions:

| Definition | Infers | And also |
|------------|--------|----------|
| `velocity = length / time` | `length / time → velocity` | `velocity * time → length` |
| `area = length * length` | `length * length → area` | `area / length → length` |
| `force = mass * acceleration` | `mass * acceleration → force` | `force / mass → acceleration` |

---

## Related Specifications

- [Syntax](syntax.md)
- [Data Structures](data_structures.md)
- [Memory and Ownership](memory.md)
- [Primitive as Object](primitive_as_obj.md)

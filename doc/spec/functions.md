# Simple Language Functions and Pattern Matching

> **📤 EXTRACTED:** Test cases have been extracted to an executable test file:  
> **→** `tests/specs/functions_spec.spl`  
> **Date:** 2026-01-09  
> **Type:** Category B (Extract + Keep)
> 
> This file remains as **architectural reference documentation**.  
> Test cases and examples are in the _spec.spl file for execution and validation.

This document covers functions, lambdas, closures, pattern matching, and constructor polymorphism.

## Related Specifications

- [Async Default](async_default.md) - Async-by-default function model
- [Suspension Operator](suspension_operator.md) - Explicit `~` suspension syntax
- [Concurrency](concurrency.md) - Futures, actors, channels

---

## Functions

Functions in Simple are defined with the `fn` keyword. The syntax is inspired by Python's definition style and Rust's explicitness.

### Basic Function Definition

```simple
fn add(a: i64, b: i64) -> i64:
    return a + b
```

This defines a function `add` that takes two Ints and returns an Int. If the return type can be inferred, it might be optional. If a function does not explicitly return a value, it returns `nil` (unit type).

### Async/Sync Effect Modifiers

Functions have an **inferred async/sync effect** based on their body:

```simple
# Inferred as SYNC: only pure computation
fn double(x: i64) -> i64:
    return x * 2

# Inferred as ASYNC: uses suspension operator
fn fetch_user(id: UserId) -> User:
    let user ~= http.get("/users/{id}")
    return user

# Explicit SYNC: compiler verifies no suspension
sync fn compute(x: i64) -> i64:
    return x * x

# Explicit ASYNC: documentation, no behavioral change
async fn load_data() -> Data:
    let d ~= read_file(path)
    return d
```

**Effect Inference Rules:**

| Body Contains | Inferred Effect | Return Type |
|---------------|-----------------|-------------|
| `~=`, `if~`, `while~` | async | `Promise[T]` |
| Calls to async functions | async | `Promise[T]` |
| Only sync operations | sync | `T` directly |

See [Async Default](async_default.md) for complete effect inference specification.

### First-Class Functions

Simple supports first-class functions - you can assign functions to variables or pass them as arguments:

```simple
let math_op = add
let result = math_op(2, 3)  # 5

fn apply(f: fn(i64, i64) -> i64, x: i64, y: i64) -> i64:
    return f(x, y)

apply(add, 10, 20)  # 30
```

---

## Lambdas and Closures

### Lambda Syntax

An inline lambda uses a backslash to introduce parameters (inspired by ML-family languages):

```simple
let square = \x: x * x
let double = \x: x * 2

# With explicit type annotations
let typed_square = \(x: i64) -> i64: x * x
```

The backslash syntax was chosen for one-pass parsing - seeing `\` immediately signals a lambda, requiring only single-token lookahead.

### Multiple Parameters

```simple
let add = \a, b: a + b
let sum = add(3, 4)  # 7

# With types
let typed_add = \(a: i64, b: i64) -> i64: a + b
```

### Closures

Lambdas capture variables from their enclosing scope:

```simple
let multiplier = 3
let scale = \x: x * multiplier

scale(10)  # 30
```

### Trailing Block Syntax

Methods can accept trailing blocks for iteration or DSL constructs:

```simple
list.each \item:
    print "Item: {item}"

map.each \key, value:
    print "{key}: {value}"

# Filtering
let positives = numbers.filter \x: x > 0

# Mapping
let doubled = numbers.map \x: x * 2
```

---

## Pattern Matching

Pattern matching is a powerful feature enabling branching on the structure of data. The `match` expression is similar to switch in other languages but far more flexible.

### Basic Pattern Matching

```simple
enum Token:
    Number(value: i64)
    Plus
    Minus
    EOF

fn describe_token(tok: Token) -> String:
    match tok:
        case Number(val):
            return "Number({val})"
        case Plus:
            return "Plus sign"
        case Minus:
            return "Minus sign"
        case EOF:
            return "End of input"
```

### Pattern Types

#### Literal Patterns

```simple
match x:
    case 0:
        print "Zero"
    case 1:
        print "One"
```

#### Alternative Patterns

```simple
match x:
    case 1 | 2 | 3:
        print "Small number"
```

#### Guard Clauses

```simple
match x:
    case n if n < 0:
        print "Negative number: {n}"
    case n if n > 100:
        print "Large number: {n}"
    case n:
        print "Normal number: {n}"
```

#### Wildcard Pattern

```simple
match x:
    case 0:
        print "Zero"
    case _:
        print "Non-zero"
```

### Struct Destructuring

```simple
struct Point:
    x: f64
    y: f64

let p = Point(x: 5, y: 0)
match p:
    case Point(x: 0, y: 0):
        print "Origin"
    case Point(x: x_val, y: 0):
        print "On X axis at {x_val}"
    case Point(x: 0, y: y_val):
        print "On Y axis at {y_val}"
    case Point(x: _, y: _):
        print "Somewhere else"
```

### Tuple Destructuring

```simple
let pair = (1, "hello")
match pair:
    case (0, _):
        print "Starts with zero"
    case (n, s):
        print "Number {n} with string '{s}'"
```

### Exhaustiveness

All possibilities must be covered (exhaustive matching), otherwise the code will not compile:

```simple
enum Color:
    Red
    Green
    Blue

fn name(c: Color) -> str:
    match c:
        case Red: "red"
        case Green: "green"
        # Error: missing case Blue
```

---

## Constructor Polymorphism

Simple supports **constructor polymorphism**, allowing constructors to be passed as first-class values.

### Constructor Type

The `Constructor[T]` type represents any constructor that produces an instance of `T` or a subtype:

```simple
# Constructor[T] - type for constructors producing T or subtypes
let factory: Constructor[Widget] = Button    # Button extends Widget
let widget = factory("OK")                   # Creates a Button
```

### Basic Usage

```simple
class Widget:
    name: str

    fn new(name: str) -> Self:
        return Widget(name: name)

class Button(Widget):
    enabled: bool

    fn new(name: str, enabled: bool = true) -> Self:
        super(name)
        self.enabled = enabled

# Pass constructor as parameter
fn create_widget(ctor: Constructor[Widget], name: str) -> Widget:
    return ctor(name)

let b = create_widget(Button, "Click")    # Creates Button
let l = create_widget(Label, "Hello")     # Creates Label
```

### Compatibility Rules

Child constructors must be **compatible** with parent constructors:

1. Must accept all required parameters of parent constructor
2. Additional parameters must have default values
3. Parameter types must match or be contravariant

```simple
class Base:
    fn new(name: str, value: i32) -> Self:
        ...

class ValidChild(Base):
    # OK: has parent params + extra with default
    fn new(name: str, value: i32, extra: bool = false) -> Self:
        super(name, value)
        ...

class InvalidChild(Base):
    # ERROR: extra param without default
    fn new(name: str, value: i32, extra: bool) -> Self:  # Compile error!
        ...
```

### Compatibility Table

| Parent Constructor | Child Constructor | Valid? | Reason |
|-------------------|-------------------|--------|--------|
| `new(a: A)` | `new(a: A)` | ✓ | Same signature |
| `new(a: A)` | `new(a: A, b: B = default)` | ✓ | Extra with default |
| `new(a: A)` | `new(a: A, b: B)` | ✗ | Extra without default |
| `new(a: A)` | `new()` | ✗ | Missing required |
| `new(a: A, b: B = x)` | `new(a: A)` | ✓ | Parent default used |

### Factory Patterns

```simple
# Generic factory function
fn create_many[T](ctor: Constructor[T], names: [str]) -> [T]:
    return [ctor(name) for name in names]

let buttons = create_many(Button, ["OK", "Cancel", "Help"])

# Factory selector
fn get_widget_factory(kind: str) -> Constructor[Widget]:
    match kind:
        case "button": return Button
        case "label": return Label
        case _: return Widget

let factory = get_widget_factory("button")
let w = factory("Dynamic Button")
```

### Storing Constructors

```simple
# In variables
let ctor: Constructor[Widget] = Button

# In collections
let factories: [Constructor[Widget]] = [Button, Label, Slider]

# In dictionaries
let registry: {str: Constructor[Widget]} = {
    "button": Button,
    "label": Label,
}

let widget = registry["button"]("Created from registry")
```

### Constructor Constraints

Specify exact constructor signatures:

```simple
# Constructor that takes exactly (str, i32)
fn exact_factory(ctor: Constructor[Widget, (str, i32)]) -> Widget:
    return ctor("default", 42)

# Constructor that takes no parameters
fn no_arg_factory[T](ctor: Constructor[T, ()]) -> T:
    return ctor()
```

### Dependency Injection

Constructor polymorphism enables clean dependency injection:

```simple
class Service:
    fn new(config: Config) -> Self:
        ...

class MockService(Service):
    fn new(config: Config, mock_data: Data = Data.empty()) -> Self:
        super(config)
        ...

class ProductionService(Service):
    fn new(config: Config, pool_size: i32 = 10) -> Self:
        super(config)
        ...

class Application:
    service: Service

    fn new(service_ctor: Constructor[Service], config: Config) -> Self:
        self.service = service_ctor(config)

# Production
let app = Application(ProductionService, prod_config)

# Testing
let test_app = Application(MockService, test_config)
```

### Abstract Constructors

Use traits to define abstract constructor requirements:

```simple
trait Creatable:
    fn create(name: str) -> Self

impl Creatable for Widget:
    fn create(name: str) -> Widget:
        return Widget.new(name)

fn make[T: Creatable](name: str) -> T:
    return T.create(name)
```

---

## Semantic Types in Function Signatures

Public functions should use semantic types (unit types, enums, Option) instead of bare primitives. See [Unit Types](units.md) for the complete policy.

```simple
# WARNING: Bare primitives in public API
pub fn get_user_id() -> i64:        # Warning: use unit type
    return 42

# GOOD: Semantic types (no warning)
pub fn get_user_id() -> UserId:     # OK
    return 42_uid

# GOOD: Enums instead of bool
pub fn set_status(status: UserStatus):  # OK
    ...

# GOOD: Option for nullable returns
pub fn find_user(id: UserId) -> Option[User]:  # OK
    ...
```

---

## Related Specifications

- [Syntax](syntax.md)
- [Types](types.md)
- [Unit Types](units.md)
- [Data Structures](data_structures.md)
- [Traits](traits.md)

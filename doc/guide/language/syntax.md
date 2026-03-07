# Simple Language Syntax Guide

This guide covers core syntax elements: constructors, methods, lambdas, collections, and special blocks.

---

## Variables and Bindings

```simple
val name = "Alice"                    # Immutable (preferred)
name := "Alice"                       # Walrus operator (:= is val synonym)
var count = 0                         # Mutable

val x: i32 = 42                       # Explicit type annotation
```

---

## Constructors

Simple provides **zero-boilerplate constructors**. Declare a struct and use it immediately -- no `__init__`, no `new` method required.

### Direct Construction (Primary Pattern)

```simple
struct Point:
    x: i64
    y: i64

val p1 = Point(3, 4)                 # Positional arguments
val p2 = Point(x: 10, y: 20)         # Named parameters
```

This works immediately without any `impl` block. Use named parameters for clarity when you have 3+ fields.

### Static Constructor Methods

Add `fn new()` or other factory methods when you need validation, defaults, or custom logic:

```simple
impl Point:
    fn new(x: i64, y: i64) -> Point:
        return Point(abs(x), abs(y))

    fn origin() -> Point:
        return Point(0, 0)

    fn from_tuple(t: (i64, i64)) -> Point:
        return Point(t.0, t.1)

val p = Point.new(-3, 4)             # Normalized to (3, 4)
val o = Point.origin()               # (0, 0)
```

**Implicitly static names**: The following function names are automatically treated as static (no `static` keyword needed at module level):
- `new`, `create`, `default`, `init`
- Any name starting with `from_` or `with_`

You can also use explicit `static fn` for maximum clarity:

```simple
impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x, y)
```

### Validated Constructor

Return `Option` or `Result` when construction can fail:

```simple
struct Age:
    value: i64

impl Age:
    fn new(value: i64) -> Option<Age>:
        if value >= 0 and value <= 150:
            return Some(Age(value))
        return None

match Age.new(25):
    Some(age): print "Valid: {age.value}"
    None: print "Invalid age"
```

### Builder Pattern

Use fluent setters for types with many optional parameters:

```simple
struct Config:
    host: text
    port: i64
    timeout: i64

impl Config:
    fn default() -> Config:
        return Config(host: "localhost", port: 8080, timeout: 30)

    me with_host(host: text) -> Config:
        self.host = host
        return self

    me with_port(port: i64) -> Config:
        self.port = port
        return self

val cfg = Config.default()
    .with_host("example.com")
    .with_port(9000)
```

### Constructor Decision Guide

| Situation | Recommended Pattern |
|-----------|-------------------|
| Simple data object | Direct: `Point(3, 4)` |
| Need validation | `fn new() -> Option<T>` or `Result<T, E>` |
| Factory methods | `fn from_string()`, `fn square()` |
| Many optional params | Builder: `fn default()` + `fn with_*()` |
| Inside local scope | Direct construction or explicit `static fn` |

---

## Methods

Simple has three method kinds, distinguished by their relationship to `self`:

### Static Methods (No Self)

```simple
impl Point:
    static fn origin() -> Point:
        return Point(0, 0)

val o = Point.origin()
```

### Immutable Methods (fn)

Implicit `self` parameter with read-only access:

```simple
impl Point:
    fn distance_from_origin() -> f64:
        return sqrt(self.x * self.x + self.y * self.y)
```

### Mutable Methods (me)

Use `me` keyword to declare methods that modify `self`:

```simple
impl Point:
    me move_by(dx: i64, dy: i64):
        self.x = self.x + dx
        self.y = self.y + dy
```

### Calling Syntax

Use dot syntax for all method calls:

```simple
val p = Point.origin()                # Static method
val d = p.distance_from_origin()      # Instance method
p.move_by(1, 2)                       # Mutable method
```

---

## Functions

```simple
fn square(x: i64) -> i64:
    x * x                             # Implicit return (last expression)

fn greet(name: text):
    print "Hello, {name}!"            # No return type = void

fn divide(a: i64, b: i64) -> Result<i64, text>:
    if b == 0:
        return Err("division by zero")
    Ok(a / b)
```

---

## Lambda Expressions

Simple supports three equivalent lambda syntaxes:

| Syntax | Example | Style |
|--------|---------|-------|
| `fn():` | `fn(x): x * 2` | Function-like |
| `\:` | `\x: x * 2` | Concise |
| `_` placeholder | `_ * 2` | Shortest |

### fn() Syntax

```simple
val doubled = numbers.map(fn(x): x * 2)
val evens = numbers.filter(fn(x): x % 2 == 0)

# No parameters
val supplier = fn(): 42

# Multi-line body
val transform = fn(x):
    val step1 = x * 2
    val step2 = step1 + 10
    step2
```

### Backslash Syntax

```simple
val doubled = numbers.map(\x: x * 2)
val add = \x, y: x + y
```

### Placeholder Syntax

```simple
items.map(_ * 2)                      # Single parameter
items.map(_1 + _2)                    # Numbered placeholders
words.map(&:len)                      # Method reference
```

### Closure and Nesting

```simple
fn make_adder(x: i64):
    return fn(y): x + y               # Captures x from outer scope

val add_5 = make_adder(5)
val result = add_5(3)                 # 8
```

---

## String Interpolation

```simple
print "Hello, {name}!"               # Default: interpolated
print r"raw: \d+"                     # Raw string (no interpolation)
```

---

## Pattern Matching

```simple
match value:
    Some(x): process(x)
    None: handle_missing()

match shape:
    Circle(r): pi * r * r
    Rectangle(w, h): w * h
```

---

## Optional Chaining and Coalescing

```simple
user?.name                            # Optional chaining
user?.profile?.email                  # Chained navigation
name ?? "Anonymous"                   # Nil coalescing
user?.name ?? "Unknown"               # Combined
```

---

## Comprehensions

```simple
[for x in 0..10 if x % 2 == 0: x]           # List comprehension
[for x in items: x * 2]                      # Map-style
[for x in items if x > 0: x]                 # Filter-style
```

---

## Operators

| Operator | Purpose | Example |
|----------|---------|---------|
| `\|>` | Pipe | `data \|> transform \|> display` |
| `>>` | Compose | `parse >> validate >> save` |
| `~>` | Layer connect | Neural network layers |
| `**` | Power | `2 ** 10` |
| `?` | Error propagation | `file_read(path)?` |
| `m{ }` | Math block | `m{ x^2 + y^2 }` |

---

## Collection Literals

### Arrays

```simple
val nums = [1, 2, 3]                 # Array<i64>
val empty: [i64] = []                # Empty array with type
```

### Dictionaries

```simple
val data = {"key": "value", "count": 42}
```

### Sets

```simple
val nums = s{1, 2, 3}               # Set<i64>
val words = s{"hello", "world"}      # Set<text>
val empty: Set<i64> = s{}            # Empty set (type annotation required)
```

Sets automatically deduplicate elements:

```simple
val nums = s{1, 2, 2, 3}            # Only {1, 2, 3}
```

#### Set Operations

```simple
val a = s{1, 2, 3}
val b = s{2, 3, 4}

val union = a.union(b)               # {1, 2, 3, 4}
val common = a.intersect(b)          # {2, 3}
val diff = a.diff(b)                 # {1}
val sym = a.sym_diff(b)              # {1, 4}

if a.has(2):
    print "Found"
```

---

## Generic Types

```simple
struct Container<T>:
    value: T

impl<T> Container<T>:
    static fn new(value: T) -> Container<T>:
        return Container(value: value)

    fn get() -> T:
        return self.value

val int_box = Container.new(42)      # T inferred as i64
val str_box = Container.new("hello") # T inferred as text
```

Use angle brackets `<>` for generics (not `[]`):

```simple
List<i64>                            # Correct
Option<text>                         # Correct
```

---

## Enums and Variants

```simple
enum Color:
    Red
    Green
    Blue

enum Option<T>:
    Some(T)
    None

val opt = Some(42)
val none = None
```

---

## Traits

```simple
trait Serializable:
    fn serialize() -> text

trait Comparable:
    fn compare(other: Self) -> i64

# Multiple trait bounds
fn process<T: Serializable & Comparable>(item: T):
    val json = item.serialize()
```

---

## Lean Verification Blocks

Embed Lean 4 formal proofs directly in Simple source:

```simple
lean{
theorem add_comm : forall a b : Nat, a + b = b + a := by
    omega
}

fn add(a: i64, b: i64) -> i64:
    a + b
```

Import external Lean files:

```simple
lean import "proofs/math_lemmas.lean"
```

Contracts on `@verify` functions are automatically converted to Lean theorems:

```simple
@verify
fn divide(a: i64, b: i64) -> i64:
    in: b != 0
    out(result): result * b == a
    a / b
```

---

## Special Markers

```simple
pass_todo                             # Marks unimplemented code
pass_do_nothing                       # Intentional no-op
pass_dn                               # Alias for pass_do_nothing
```

---

## Struct, Class, and Type Aliases

```simple
struct Point:                         # Value type
    x: i64
    y: i64

class Person:                         # Reference type
    name: text
    age: i64

type Point2D = Point                  # Type alias
alias Optional = Option               # Class alias
```

Note: Simple does **not** support inheritance. Use composition, traits, or mixins instead.

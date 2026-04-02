# Simple Language Type System

This guide covers type inference, advanced types, type checking, and newtype patterns.

---

## Type Inference

Simple uses Hindley-Milner type inference with bidirectional checking. Most types are inferred automatically.

### Literal Inference

```simple
val x = 42          # i64
val y = 3.14        # f64
val z = "hello"     # text
val b = true        # bool
```

### Function Return Inference

```simple
fn double(x: i64):
    x * 2           # Return type inferred as i64

fn identity<T>(x: T) -> T:
    x
```

### Generic Instantiation

```simple
val n = identity(42)        # T inferred as i64
val s = identity("hello")   # T inferred as text
```

### Bidirectional Inference

Expected types propagate to expressions:

```simple
val numbers: [i32] = [1, 2, 3]       # Array element type inferred as i32 here
val add: fn(i64, i64) -> i64 = \x, y: x + y   # Parameters inferred from type
```

### When to Add Annotations

| Context | Annotations |
|---------|-------------|
| Public function signatures | Required |
| Struct/class fields | Required |
| Generic constraints | Required |
| Local variables (library code) | Recommended |
| Local variables (application code) | Optional |
| Lambda parameters | Contextual |

```simple
# Explicit when needed for a specific type
val bytes: [u8] = [0, 1, 2]          # Need u8, not default i64

# Explicit for documentation
fn distance(x: f64, y: f64) -> f64:
    (x * x + y * y).sqrt()
```

---

## Type Checking

### Running the Type Checker

```bash
simple check src/main.spl             # Check a file
simple check --show-types src/lib.spl # Show inferred types
simple check --verbose src/*.spl      # Verbose with suggestions
```

Type checking is optional -- it only runs when you use `simple check` or `--type-check` flags.

### Forward References

Functions can be called before they are defined:

```simple
fn main():
    val result = helper()             # helper() defined below -- OK
    print result

fn helper() -> i64:
    42
```

### Mutual Recursion

```simple
fn is_even(n: i64) -> bool:
    if n == 0: true
    else: is_odd(n - 1)

fn is_odd(n: i64) -> bool:
    if n == 0: false
    else: is_even(n - 1)
```

### Optional Chaining Types

```simple
val user: User? = get_user()          # Option<User>
val name: text? = user?.name          # Option<text>
val display: text = name ?? "Unknown" # text (not optional)
```

---

## Union Types

A union type means a value can be one of several types:

```simple
type IntOrText = i64 | text
type OptionalInt = i64 | nil

fn divide(a: i64, b: i64) -> i64 | nil:
    if b == 0:
        return nil
    a / b
```

### Pattern Matching on Unions

```simple
fn process_value(value: i64 | text):
    if value is i64:
        print "Integer: {value}"
    else:
        print "Text: {value}"
```

---

## Intersection Types (Trait Bounds)

Intersection types express "must satisfy all" constraints:

```simple
trait Serializable:
    fn serialize() -> text

trait Comparable:
    fn compare(other: Self) -> i64

fn process<T: Serializable & Comparable>(item: T):
    val json = item.serialize()
    val order = item.compare(item)

type DataStore = Readable & Writable & Closeable
```

---

## Refinement Types

Refinement types add runtime predicates to values:

```simple
type PositiveInt = x: i64 where x > 0
type NonEmptyText = s: text where len(s) > 0
type BoundedValue = v: i64 where v >= 0 and v < 100
```

### Usage in Function Signatures

```simple
fn sqrt(x: i64 where x >= 0) -> f64:
    math.sqrt(float(x))

fn set_volume(level: i64 where level >= 0 and level <= 100):
    audio.volume = level

fn first<T>(arr: List<T> where len(arr) > 0) -> T:
    arr[0]
```

### Supported Predicates

- **Integer comparisons**: `x > 0`, `x >= 0 and x < 100`
- **Length constraints**: `len(s) > 0`, `len(arr) <= 10`
- **Float comparisons**: `f > 0.0`, `f >= 0.0 and f <= 1.0`

---

## Generics

### Basic Generics

```simple
fn identity<T>(x: T) -> T:
    x

fn pair<A, B>(a: A, b: B) -> (A, B):
    (a, b)
```

### Constrained Generics

```simple
fn compare<T: Comparable>(a: T, b: T) -> i64:
    a.compare(b)

fn sort_and_hash<T: Comparable & Hashable>(items: List<T>):
    items.sort()
    for item in items:
        print item.hash()
```

### Polymorphic Types

```simple
val opt_num: Option<i64> = Some(42)
val opt_str: Option<text> = Some("hello")
```

---

## Newtype Patterns

Use newtypes (via the `unit` keyword) to add semantic meaning and prevent parameter swap bugs.

### When to Create a Newtype

Create a newtype when:
- **Semantic distinction prevents bugs** (Metallic vs Roughness)
- **Values have physical meaning or units** (Milliseconds, ByteCount)
- **Helper methods add domain operations**

```simple
unit Metallic: f32 as metallic
unit Roughness: f32 as roughness

# Compiler prevents: set_material(roughness, metallic)
fn set_material(metallic: Metallic, roughness: Roughness):
    pass_todo
```

### When to Keep Primitives

Keep bare primitives when:
- External specifications require them (JSON, HTTP)
- Generic math operations (`lerp`, `sin`)
- Boolean predicates (`is_empty() -> bool`)
- FFI boundaries
- Collection indexing (`get(index: i64)`)

### Newtype with Helpers

```simple
unit Milliseconds: u64 as ms

impl Milliseconds:
    fn from_u64(n: u64) -> Milliseconds:
        return n_ms

    fn value() -> u64:
        return self as u64

    fn to_seconds() -> Seconds:
        return (self.value() / 1000)_s

    fn seconds(n: u64) -> Milliseconds:
        return (n * 1000)_ms
```

### Enum for Finite Modes

Use enums instead of magic numbers:

```simple
pub enum ShutdownMode:
    Read
    Write
    Both

impl ShutdownMode:
    fn to_i64() -> i64:
        match self:
            case Read: 0
            case Write: 1
            case Both: 2
```

### Naming Conventions for Newtypes

| Suffix | Meaning | Example |
|--------|---------|---------|
| `Count` | Number of items | `ByteCount`, `TokenCount` |
| `Index` | Position in collection | `VertexIndex`, `LightIndex` |
| `Size` | Dimension or capacity | `TextureSize`, `BufferSize` |
| `Id` | Unique identifier | `SessionId`, `StateId` |
| Time units | Duration measure | `Milliseconds`, `Seconds` |

---

## Traits and Implementations

```simple
trait Show:
    fn show() -> text

impl Show for i64:
    fn show() -> text: "integer"

# The type checker prevents duplicate implementations
```

---

## Type Aliases

```simple
type Point2D = Point                  # Type alias
alias Optional = Option               # Class alias
```

---

## Error Messages

### Type Mismatch

```
Type error: Expected i64, Found text
```

### Undefined Identifier

```
Type error: Undefined identifier 'foo'
Hint: Check if 'foo' is imported or defined
```

### Occurs Check Failed

Indicates an infinite type (e.g., `T = List<T>`). Simplify recursive type definitions or add explicit annotations.

---

## Best Practices

1. **Let inference work** -- add annotations only when needed for clarity or disambiguation
2. **Use refinement types for input validation** instead of manual checks scattered in function bodies
3. **Prefer union types** (`i64 | nil`) over custom wrapper classes for optional values
4. **Use intersection types** (`Serializable & Comparable`) for multiple trait bounds
5. **Create newtypes for domain concepts** that prevent parameter confusion, not for wrapping all primitives
6. **Use pattern matching** to handle all enum/option cases instead of `.unwrap()`

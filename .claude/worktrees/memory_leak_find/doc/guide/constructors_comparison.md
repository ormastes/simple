# Constructor Syntax: Simple vs Other Languages

A comparison of constructor patterns across Simple, Python, Ruby, Rust, and JavaScript.

## Quick Comparison Table

| Language | Constructor Syntax | Auto Constructor | Static Method | Instance Method |
|----------|-------------------|------------------|---------------|-----------------|
| **Simple** | `Type(args)` ✅ **or** `Type.new(args)` | ✅ **Yes** | `fn new()` (implicit static)<br>`static fn new()` (explicit) | `fn method()` (immutable)<br>`me method()` (mutable) |
| **Python** | `Type(args)` | ❌ No | `@staticmethod` | `def method(self):` |
| **Ruby** | `Type.new(args)` | ❌ No | `def self.method` | `def method` |
| **Rust** | `Type::new(args)` | ❌ No | `fn new()` in impl | `fn method(&self)` / `fn method(&mut self)` |
| **JavaScript** | `new Type(args)` | ❌ No | `static method()` | `method()` |

**Simple's Advantage:** Only language with **zero-boilerplate constructors** - declare struct, use immediately like Python!

## Side-by-Side Examples

### Basic Constructor

<table>
<tr><th>Simple</th><th>Python</th><th>Ruby</th><th>Rust</th><th>JavaScript</th></tr>
<tr><td>

```simple
struct Point:
    x: i64
    y: i64

# ✅ PRIMARY: Zero boilerplate!
val p = Point(3, 4)

# ✅ OPTIONAL: Custom logic
impl Point:
    # fn new() is implicitly static at module level
    fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)

val p2 = Point.new(3, 4)
```

</td><td>

```python
class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y




p = Point(3, 4)
```

</td><td>

```ruby
class Point
  attr_accessor :x, :y

  def initialize(x, y)
    @x = x
    @y = y
  end
end

p = Point.new(3, 4)
```

</td><td>

```rust
struct Point {
    x: i64,
    y: i64,
}

impl Point {
    fn new(x: i64, y: i64) -> Self {
        Point { x, y }
    }
}

let p = Point::new(3, 4);
```

</td><td>

```javascript
class Point {
  constructor(x, y) {
    this.x = x;
    this.y = y;
  }
}



const p = new Point(3, 4);
```

</td></tr>
</table>

### Multiple Constructors / Factory Methods

<table>
<tr><th>Simple</th><th>Python</th><th>Ruby</th><th>Rust</th><th>JavaScript</th></tr>
<tr><td>

```simple
impl Point:
    # Implicit static - no keyword needed!
    fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)

    fn origin() -> Point:
        return Point(0, 0)

    fn from_tuple(t: (i64, i64)) -> Point:
        return Point(t.0, t.1)
```

</td><td>

```python
class Point:
    def __init__(self, x, y):
        self.x, self.y = x, y

    @staticmethod
    def origin():
        return Point(0, 0)
```

</td><td>

```ruby
class Point
    def initialize(x, y)
        @x, @y = x, y
    end

    def self.origin
        Point.new(0, 0)
    end
end
```

</td><td>

```rust
impl Point {
    fn new(x: i64, y: i64) -> Self {
        Point { x, y }
    }

    fn origin() -> Self {
        Point { x: 0, y: 0 }
    }
}
```

</td><td>

```javascript
class Point {
    constructor(x, y) {
        this.x = x;
        this.y = y;
    }

    static origin() {
        return new Point(0, 0);
    }
}
```

</td></tr>
</table>

### Instance Methods

<table>
<tr><th>Simple</th><th>Python</th><th>Ruby</th><th>Rust</th><th>JavaScript</th></tr>
<tr><td>

```simple
impl Point:
    # Immutable
    fn distance() -> f64:
        return sqrt(
            self.x * self.x +
            self.y * self.y
        )

    # Mutable
    me move(dx: i64, dy: i64):
        self.x += dx
        self.y += dy
```

</td><td>

```python
class Point:
    def distance(self):
        return math.sqrt(
            self.x ** 2 +
            self.y ** 2
        )


    def move(self, dx, dy):
        self.x += dx
        self.y += dy
```

</td><td>

```ruby
class Point
    def distance
        Math.sqrt(
            @x ** 2 +
            @y ** 2
        )
    end


    def move(dx, dy)
        @x += dx
        @y += dy
    end
end
```

</td><td>

```rust
impl Point {
    fn distance(&self) -> f64 {
        (self.x.pow(2) +
         self.y.pow(2))
            as f64.sqrt()
    }

    fn move(&mut self, dx: i64, dy: i64) {
        self.x += dx;
        self.y += dy;
    }
}
```

</td><td>

```javascript
class Point {
    distance() {
        return Math.sqrt(
            this.x ** 2 +
            this.y ** 2
        );
    }

    move(dx, dy) {
        this.x += dx;
        this.y += dy;
    }
}
```

</td></tr>
</table>

### Builder Pattern

<table>
<tr><th>Simple</th><th>Python</th><th>Ruby</th><th>Rust</th><th>JavaScript</th></tr>
<tr><td>

```simple
struct Config:
    host: String
    port: i64

impl Config:
    static fn new() -> Config:
        return Config(
            host: "localhost",
            port: 8080
        )

    me with_host(host: String) -> Config:
        self.host = host
        return self

val cfg = Config.new()
    .with_host("example.com")
```

</td><td>

```python
class Config:
    def __init__(self):
        self.host = "localhost"
        self.port = 8080




    def with_host(self, host):
        self.host = host
        return self

cfg = (Config()
    .with_host("example.com"))
```

</td><td>

```ruby
class Config
  def initialize
    @host = "localhost"
    @port = 8080
  end




  def with_host(host)
    @host = host
    self
  end
end

cfg = Config.new
    .with_host("example.com")
```

</td><td>

```rust
struct Config {
    host: String,
    port: i64,
}

impl Config {
    fn new() -> Self {
        Config {
            host: "localhost".into(),
            port: 8080
        }
    }

    fn with_host(mut self, host: String) -> Self {
        self.host = host;
        self
    }
}

let cfg = Config::new()
    .with_host("example.com".into());
```

</td><td>

```javascript
class Config {
  constructor() {
    this.host = "localhost";
    this.port = 8080;
  }




  withHost(host) {
    this.host = host;
    return this;
  }
}

const cfg = new Config()
    .withHost("example.com");
```

</td></tr>
</table>

### Generic Types

<table>
<tr><th>Simple</th><th>Python</th><th>Ruby</th><th>Rust</th><th>JavaScript</th></tr>
<tr><td>

```simple
struct Box<T>:
    value: T

impl<T> Box<T>:
    static fn new(value: T) -> Box<T>:
        return Box(value: value)

    fn get() -> T:
        return self.value

val b = Box.new(42)
```

</td><td>

```python
from typing import TypeVar, Generic

T = TypeVar('T')

class Box(Generic[T]):
    def __init__(self, value: T):
        self.value = value

    def get(self) -> T:
        return self.value

b = Box(42)
```

</td><td>

```ruby
# Ruby has no static typing
class Box
    def initialize(value)
        @value = value
    end

    def get
        @value
    end
end

b = Box.new(42)
```

</td><td>

```rust
struct Box<T> {
    value: T,
}

impl<T> Box<T> {
    fn new(value: T) -> Self {
        Box { value }
    }

    fn get(&self) -> &T {
        &self.value
    }
}

let b = Box::new(42);
```

</td><td>

```javascript
// No native generics
class Box {
  constructor(value) {
    this.value = value;
  }

  get() {
    return this.value;
  }
}

const b = new Box(42);
```

</td></tr>
</table>

## Key Differences

### Simple vs Python

| Feature | Simple | Python |
|---------|--------|--------|
| Constructor call | `Type(args)` (primary) or `Type.new(args)` | `Type()` (calls `__init__`) |
| Self reference | Implicit `self` | Explicit `self` in parameters |
| Mutability | `me` keyword for mutable | All methods can mutate |
| Static methods | `static fn new()` | `@staticmethod` decorator |
| Return type | Explicit | Optional (type hints) |

### Simple vs Ruby

| Feature | Simple | Ruby |
|---------|--------|--------|
| Constructor call | `Type(args)` (primary) or `Type.new(args)` | `Type.new` (calls `initialize`) |
| Self reference | Implicit `self` | Implicit `self`, use `@var` |
| Static methods | `static fn method` | `def self.method` |
| Type annotations | Required for function params | Not available |
| Return value | Explicit `return` | Last expression (implicit) |

### Simple vs Rust

| Feature | Simple | Rust |
|---------|--------|--------|
| Constructor call | `Type(args)` (primary) or `Type.new()` (dot) | `Type::new()` (double-colon) |
| Method syntax | `fn method()` / `me method()` | `fn method(&self)` / `fn method(&mut self)` |
| Self reference | Implicit | Explicit (`&self`, `&mut self`, `self`) |
| Ownership | GC-based | Ownership/borrowing |
| Similarity | ⭐⭐⭐⭐⭐ Most similar | - |

**Note:** Simple's syntax is heavily inspired by Rust but uses dot syntax and implicit self.

### Simple vs JavaScript

| Feature | Simple | JavaScript |
|---------|--------|--------|
| Constructor call | `Type(args)` (primary) or `Type.new()` | `new Type()` |
| Constructor method | `static fn new()` | `constructor()` |
| Static methods | `static fn method` | `static method()` |
| Type safety | Static typing | Dynamic (TypeScript adds types) |
| Method definition | In `impl` block | In `class` body |

## Philosophy Comparison

### Python
- **Duck typing**: "If it walks like a duck..."
- **Implicit is better than explicit**: Lots of magic methods
- **Batteries included**: Rich standard library

### Ruby
- **Principle of least surprise**: Intuitive syntax
- **Everything is an object**: Including classes
- **Blocks everywhere**: Powerful iteration patterns

### Rust
- **Zero-cost abstractions**: Performance without overhead
- **Memory safety without GC**: Ownership system
- **Explicit over implicit**: Clear borrowing semantics

### JavaScript
- **Prototypal inheritance**: Objects inherit from objects
- **First-class functions**: Functions are values
- **Async by default**: Event loop and promises

### Simple
- **Rust-inspired syntax**: Static typing, explicit returns
- **Python-like ergonomics**: String interpolation, comprehensions
- **Ruby-like method calls**: Dot syntax for everything
- **Explicit mutability**: `me` keyword for mutable methods
- **Memory managed**: GC-based (no manual memory management)

## Migration Guide

### From Python

```python
# Python
class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def move(self, dx, dy):
        self.x += dx
        self.y += dy

p = Point(3, 4)
p.move(1, 2)
```

```simple
# Simple
struct Point:
    x: i64
    y: i64

impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)

    me move(dx: i64, dy: i64):
        self.x = self.x + dx  # or self.x += dx
        self.y = self.y + dy

val p = Point.new(3, 4)
# Or use direct construction: val p = Point(3, 4)
p.move(1, 2)
```

**Changes:**
1. Add `.new()` to constructor call
2. Add type annotations
3. Use `static fn` for constructors
4. Use `me` for mutable methods
5. Explicit `return` statements

### From Ruby

```ruby
# Ruby
class Point
  attr_accessor :x, :y

  def initialize(x, y)
    @x, @y = x, y
  end

  def move(dx, dy)
    @x += dx
    @y += dy
  end
end

p = Point.new(3, 4)
```

```simple
# Simple
struct Point:
    x: i64
    y: i64

impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)

    me move(dx: i64, dy: i64):
        self.x += dx
        self.y += dy

val p = Point.new(3, 4)
# Or use direct construction: val p = Point(3, 4)
```

**Changes:**
1. Replace `initialize` with `static fn new`
2. Add type annotations
3. Use `self.field` instead of `@field`
4. Add `me` for mutable methods
5. Constructor call stays the same (`Type.new()`)

### From Rust

```rust
// Rust
struct Point {
    x: i64,
    y: i64,
}

impl Point {
    fn new(x: i64, y: i64) -> Self {
        Point { x, y }
    }

    fn move(&mut self, dx: i64, dy: i64) {
        self.x += dx;
        self.y += dy;
    }
}

let mut p = Point::new(3, 4);
```

```simple
# Simple
struct Point:
    x: i64
    y: i64

impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)

    me move(dx: i64, dy: i64):
        self.x += dx
        self.y += dy

val p = Point.new(3, 4)
# Or use direct construction: val p = Point(3, 4)
```

**Changes:**
1. Change `::` to `.` in constructor call
2. Remove `&self`, `&mut self` - use implicit self
3. Use `me` instead of `&mut self`
4. Use `:` for struct fields (not `,`)
5. No `let mut` - mutability is implicit

### From JavaScript

```javascript
// JavaScript
class Point {
  constructor(x, y) {
    this.x = x;
    this.y = y;
  }

  move(dx, dy) {
    this.x += dx;
    this.y += dy;
  }
}

const p = new Point(3, 4);
```

```simple
# Simple
struct Point:
    x: i64
    y: i64

impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)

    me move(dx: i64, dy: i64):
        self.x += dx
        self.y += dy

val p = Point.new(3, 4)
# Or use direct construction: val p = Point(3, 4)
```

**Changes:**
1. Replace `constructor` with `static fn new`
2. Remove `new` keyword, use `Type.new()`
3. Add type annotations
4. Define fields in struct
5. Use `me` for mutable methods
6. Use `val` instead of `const`

## Summary

**Simple's approach:**
- **Primary syntax**: Like Python (`Type(args)`) - **zero boilerplate!**
- **Alternative syntax**: Like Ruby (`Type.new(args)`)
- **Type system**: Like Rust (static, explicit)
- **Method definition**: Like Rust (impl blocks)
- **Mutability**: Like Rust (explicit with `me`)
- **Ergonomics**: Like Python (implicit returns, string interpolation)
- **Memory management**: Like Python/Ruby (GC, not Rust ownership)
- **Unique feature**: **Implicit static constructors** - `fn new()` auto-recognized

**Best fit for:**
- Python developers who want static typing + zero boilerplate
- Ruby developers who want performance + familiar syntax
- Rust developers who want GC + simpler syntax
- JavaScript developers who want type safety + clean constructors

**Learn more:**
- Detailed patterns guide: `doc/guide/constructor_patterns_guide.md`
- Implementation status: `doc/guide/constructor_implementation_status.md`
- Constructor updates: `doc/guide/constructors_updated.md`


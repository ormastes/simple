# Constructors in Simple

Simple supports **Python-style direct construction** as the **PRIMARY and RECOMMENDED** syntax. This works automatically without any `impl` block!

## Basic Constructor Syntax

### Direct Construction (Python-style) ✅ **PRIMARY METHOD**

```simple
struct Point:
    x: i64
    y: i64

# Direct construction - just call the type like Python!
val p1 = Point(3, 4)
val p2 = Point(x: 10, y: 20)  # Named parameters
```

**✅ This works immediately without any `impl` block! Just declare your struct and use it.**

### Optional: Add Custom Logic with `fn new()`

```simple
impl Point:
    # Note: 'static' keyword is OPTIONAL for new/create/default/from_* methods
    fn new(x: i64, y: i64) -> Point:  # Automatically treated as static
        # Add validation or custom logic
        return Point(x: x, y: y)

val p = Point.new(3, 4)  # Also works
```

**Note:** `fn new()`, `fn create()`, `fn default()`, and `fn from_*()` are **implicitly static** at module level - you don't need to write `static fn new()`!

⚠️ **Limitation:** Implicit static currently only works for module-level definitions. For structs defined inside functions, use direct construction or explicit `static` keyword. See `doc/guide/constructor_implementation_status.md` for details.

## Constructor Declarations in Different Languages

### Simple
```simple
# No declaration needed - automatic from struct fields!
struct Point:
    x: i64
    y: i64

# Use immediately
val p = Point(3, 4)
```

### Python
```python
class Point:
    # Constructor declaration with __init__
    def __init__(self, x, y):
        self.x = x
        self.y = y

p = Point(3, 4)
```

### Ruby
```ruby
class Point
  attr_accessor :x, :y

  # Constructor declaration with initialize
  def initialize(x, y)
    @x = x
    @y = y
  end
end

p = Point.new(3, 4)
```

### Rust
```rust
struct Point {
    x: i64,
    y: i64,
}

// Manual constructor declaration
impl Point {
    fn new(x: i64, y: i64) -> Self {
        Point { x, y }
    }
}

let p = Point::new(3, 4);
```

### Java
```java
public class Point {
    private int x;
    private int y;

    // Constructor declaration
    public Point(int x, int y) {
        this.x = x;
        this.y = y;
    }
}

Point p = new Point(3, 4);
```

### C++
```cpp
class Point {
private:
    int x;
    int y;

public:
    // Constructor declaration
    Point(int x, int y) : x(x), y(y) {}
};

Point p(3, 4);
// or: Point* p = new Point(3, 4);
```

### JavaScript/TypeScript
```javascript
class Point {
    // Constructor declaration
    constructor(x, y) {
        this.x = x;
        this.y = y;
    }
}

const p = new Point(3, 4);
```

### Go
```go
type Point struct {
    X int
    Y int
}

// Manual constructor function
func NewPoint(x, y int) Point {
    return Point{X: x, Y: y}
}

p := NewPoint(3, 4)
// or: p := Point{X: 3, Y: 4}
```

## Comparison Table: Declaration vs Usage

| Language | Constructor Declaration | Constructor Call | Auto-Generated? |
|----------|------------------------|------------------|-----------------|
| **Simple** | Struct fields only | `Point(3, 4)` | ✅ Yes |
| Python | `def __init__(self, ...)` | `Point(3, 4)` | ❌ No |
| Ruby | `def initialize(...)` | `Point.new(3, 4)` | ❌ No |
| Rust | `fn new(...) -> Self` | `Point::new(3, 4)` | ❌ No (manual) |
| Java | `public Type(...)` | `new Point(3, 4)` | ✅ Default only |
| C++ | `Type(...)` | `Point(3, 4)` | ✅ Default only |
| JavaScript | `constructor(...)` | `new Point(3, 4)` | ❌ No |
| Go | `func NewType(...)` | `NewPoint(3, 4)` | ❌ No (convention) |
| Swift | `init(...)` | `Point(3, 4)` | ✅ Memberwise |
| Kotlin | `constructor(...)` | `Point(3, 4)` | ✅ Primary |

## Simple's Approach: Best of Both Worlds

### Automatic Constructors
```simple
# 1. Declare struct - get constructor for FREE
struct Point:
    x: i64
    y: i64

# 2. Use immediately like Python
val p = Point(3, 4)
```

### Optional Custom Logic
```simple
# Add custom initialization when needed
impl Point:
    fn new(x: i64, y: i64) -> Point:  # Implicitly static!
        # Validation
        if x < 0 or y < 0:
            return Point(0, 0)  # Default to origin
        return Point(x: x, y: y)

    fn origin() -> Point:  # Also implicitly static (constructor-like name)
        return Point(0, 0)

# Both work!
val p1 = Point(3, 4)           # ✅ Direct (RECOMMENDED)
val p2 = Point.new(3, 4)       # ✅ Via new()
val p3 = Point.origin()        # ✅ Named constructor
```

## Complete Examples

### Example 1: Basic Struct (No impl needed)

<table>
<tr><th>Simple</th><th>Python</th><th>Rust</th></tr>
<tr><td>

```simple
struct Point:
    x: i64
    y: i64





val p = Point(3, 4)
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

```rust
struct Point {
    x: i64,
    y: i64,
}

// No auto constructor!
// Must add manually

let p = Point { x: 3, y: 4 };
```

</td></tr>
</table>

### Example 2: With Validation

<table>
<tr><th>Simple</th><th>Python</th><th>Rust</th></tr>
<tr><td>

```simple
struct Age:
    value: i64

impl Age:
    static fn new(value: i64) -> Option<Age>:
        if value >= 0 and value <= 150:
            return Some(Age(value))
        else:
            return None

# Usage
match Age.new(25):
    case Some(age):
        print "Valid: {age.value}"
    case None:
        print "Invalid age"
```

</td><td>

```python
class Age:
    def __init__(self, value):
        if not (0 <= value <= 150):
            raise ValueError("Invalid age")
        self.value = value




# Usage
try:
    age = Age(25)
    print(f"Valid: {age.value}")
except ValueError:
    print("Invalid age")
```

</td><td>

```rust
struct Age {
    value: i64,
}

impl Age {
    fn new(value: i64) -> Option<Self> {
        if value >= 0 && value <= 150 {
            Some(Age { value })
        } else {
            None
        }
    }
}

// Usage
match Age::new(25) {
    Some(age) =>
        println!("Valid: {}", age.value),
    None =>
        println!("Invalid age"),
}
```

</td></tr>
</table>

### Example 3: Multiple Constructors

<table>
<tr><th>Simple</th><th>Python</th><th>Rust</th></tr>
<tr><td>

```simple
struct Rectangle:
    width: i64
    height: i64

impl Rectangle:
    # Named constructors
    static fn square(size: i64) -> Rectangle:
        return Rectangle(size, size)

    static fn from_area(area: i64) -> Rectangle:
        val side = sqrt(area) as i64
        return Rectangle(side, side)

# Multiple ways to construct
val r1 = Rectangle(10, 20)        # Direct
val r2 = Rectangle.square(15)     # Square
val r3 = Rectangle.from_area(100) # From area
```

</td><td>

```python
class Rectangle:
    def __init__(self, width, height):
        self.width = width
        self.height = height

    @staticmethod
    def square(size):
        return Rectangle(size, size)

    @staticmethod
    def from_area(area):
        side = int(area ** 0.5)
        return Rectangle(side, side)

# Multiple ways to construct
r1 = Rectangle(10, 20)
r2 = Rectangle.square(15)
r3 = Rectangle.from_area(100)
```

</td><td>

```rust
struct Rectangle {
    width: i64,
    height: i64,
}

impl Rectangle {
    fn square(size: i64) -> Self {
        Rectangle {
            width: size,
            height: size
        }
    }

    fn from_area(area: i64) -> Self {
        let side = (area as f64).sqrt() as i64;
        Rectangle { width: side, height: side }
    }
}

// Must use methods
let r2 = Rectangle::square(15);
let r3 = Rectangle::from_area(100);
```

</td></tr>
</table>

### Example 4: Builder Pattern

<table>
<tr><th>Simple</th><th>Python</th><th>Rust</th></tr>
<tr><td>

```simple
struct Config:
    host: String
    port: i64
    timeout: i64

impl Config:
    static fn default() -> Config:
        return Config(
            "localhost",
            8080,
            30
        )

    me with_host(host: String) -> Config:
        self.host = host
        return self

val cfg = Config.default()
    .with_host("example.com")
```

</td><td>

```python
class Config:
    def __init__(self, host="localhost",
                 port=8080, timeout=30):
        self.host = host
        self.port = port
        self.timeout = timeout




    def with_host(self, host):
        self.host = host
        return self

cfg = Config() \
    .with_host("example.com")
```

</td><td>

```rust
struct Config {
    host: String,
    port: i64,
    timeout: i64,
}

impl Config {
    fn default() -> Self {
        Config {
            host: "localhost".into(),
            port: 8080,
            timeout: 30,
        }
    }

    fn with_host(mut self, host: String) -> Self {
        self.host = host;
        self
    }
}

let cfg = Config::default()
    .with_host("example.com".into());
```

</td></tr>
</table>

## Key Advantages of Simple's Approach

### 1. No Boilerplate ✅

**Simple:**
```simple
struct Point:
    x: i64
    y: i64

val p = Point(3, 4)  # Works immediately!
```

**Python (requires boilerplate):**
```python
class Point:
    def __init__(self, x, y):  # Must write this
        self.x = x
        self.y = y

p = Point(3, 4)
```

### 2. Familiar Python Syntax ✅

```simple
# Looks like Python
val p = Point(3, 4)
val rect = Rectangle(10, 20)
val config = Config("localhost", 8080)
```

### 3. Optional Customization ✅

```simple
# Add custom logic only when needed
impl Point:
    static fn new(x: i64, y: i64) -> Point:
        # Add validation here
        return Point(x, y)
```

### 4. Named Parameters ✅

```simple
# Both work
val p1 = Point(3, 4)
val p2 = Point(x: 3, y: 4)  # Named for clarity
```

## Best Practices

### 1. Use Direct Construction by Default

```simple
# ✅ Preferred
val p = Point(3, 4)

# ❌ Unnecessary
impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)  # Just extra code!

val p = Point.new(3, 4)  # Why?
```

### 2. Add `new()` Only for Logic

```simple
# ✅ Good - adds value
impl Point:
    static fn new(x: i64, y: i64) -> Point:
        # Normalize negative values
        return Point(abs(x), abs(y))

# ✅ Good - validation
impl Age:
    static fn new(value: i64) -> Option<Age>:
        if value >= 0 and value <= 150:
            return Some(Age(value))
        return None
```

### 3. Use Named Constructors for Variants

```simple
# ✅ Good - clear intent
impl Rectangle:
    static fn square(size: i64) -> Rectangle:
        return Rectangle(size, size)

val sq = Rectangle.square(10)
```

### 4. Named Parameters for Clarity

```simple
# When many parameters, use names
struct Config:
    host: String
    port: i64
    timeout: i64
    retries: i64

# ✅ Clear
val cfg = Config(
    host: "localhost",
    port: 8080,
    timeout: 30,
    retries: 3
)

# ❌ Unclear
val cfg = Config("localhost", 8080, 30, 3)
```

## Summary

| Feature | Simple | Python | Rust |
|---------|--------|--------|------|
| Auto constructor | ✅ Yes | ❌ No | ❌ No |
| Call syntax | `Type(args)` ✅ PRIMARY | `Type(args)` | `Type::new(args)` |
| Named params | ✅ Yes | ✅ Yes (kwargs) | ❌ No |
| Custom logic | Optional `fn new()` (implicitly static) | Required `__init__` | Required `static fn new()` |
| Boilerplate | **Zero** | Medium | Medium |
| Implicit static | ✅ Yes (`new`, `create`, `default`, `from_*`) | N/A | ❌ No |

**Simple = Python's ergonomics + Rust's type safety + Zero boilerplate + Smart static inference**


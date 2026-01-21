# Constructor Patterns Guide

A practical guide to choosing the right constructor pattern in Simple.

## The Three Patterns

Simple supports three constructor patterns, each with different use cases:

### 1. 🏆 Direct Construction (Primary Pattern)

```simple
struct Point:
    x: i64
    y: i64

val p = Point(3, 4)
val p2 = Point(x: 10, y: 20)  # Named parameters
```

**When to use:**
- ✅ Default choice for all simple data types
- ✅ When you don't need validation or custom logic
- ✅ In local scopes (inside functions)
- ✅ For DTOs, configuration objects, simple value types

**Advantages:**
- Zero boilerplate - declare struct, use immediately
- Works everywhere (module and local scope)
- Python-style familiarity
- Named parameters supported

### 2. 🆕 Implicit Static Constructor

```simple
impl Point:
    fn new(x: i64, y: i64) -> Point:  # No 'static' needed!
        # Add validation or defaults
        return Point(abs(x), abs(y))

    fn origin() -> Point:
        return Point(0, 0)

    fn from_tuple(t: (i64, i64)) -> Point:
        return Point(t.0, t.1)
```

**When to use:**
- ✅ At module level when you need custom logic
- ✅ For validation, normalization, or computed defaults
- ✅ Named constructors for semantic clarity

**Advantages:**
- Less boilerplate than explicit `static`
- Constructor names auto-recognized: `new`, `create`, `default`, `from_*`, `with_*`
- Clear factory method pattern

**Limitation:**
- ⚠️ Only works at module level (not inside functions)

### 3. 📝 Explicit Static Constructor

```simple
impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x, y)

    static fn from_string(s: text) -> Option<Point>:
        # Parse and return Point or None
        ...
```

**When to use:**
- ✅ When you want maximum clarity
- ✅ In local scopes where implicit static doesn't work
- ✅ When following team coding standards

**Advantages:**
- Works everywhere (module and local scope)
- Explicit and self-documenting
- Compatible with all Simple versions

## Decision Tree

```
Do you need custom constructor logic (validation, defaults, etc.)?
├─ NO → Use Direct Construction: Point(3, 4)
│
└─ YES
   ├─ Is this at module level?
   │  ├─ YES → Use Implicit Static: fn new()
   │  └─ NO (local scope)
   │     ├─ Can you refactor to module level? → Do that
   │     └─ Otherwise → Use Explicit Static: static fn new()
   │
   └─ Do you want factory methods with semantic names?
      └─ Use Implicit Static: fn from_string(), fn with_capacity()
```

## Real-World Examples

### Example 1: Simple Data Transfer Object

```simple
# DTO for API response - no logic needed
struct UserProfile:
    id: i64
    username: text
    email: text

# ✅ Direct construction - perfect choice
val profile = UserProfile(
    id: 123,
    username: "alice",
    email: "alice@example.com"
)
```

### Example 2: Validated Value Type

```simple
# Age must be in valid range
struct Age:
    value: i64

impl Age:
    fn new(value: i64) -> Option<Age>:
        if value >= 0 and value <= 150:
            return Some(Age(value))
        else:
            return None

# ✅ Implicit static - adds validation
match Age.new(25):
    case Some(age):
        print "Valid age: {age.value}"
    case None:
        print "Invalid age"
```

### Example 3: Builder with Defaults

```simple
# Configuration with sensible defaults
struct ServerConfig:
    host: text
    port: i64
    timeout: i64
    retries: i64

impl ServerConfig:
    fn default() -> ServerConfig:
        return ServerConfig(
            host: "localhost",
            port: 8080,
            timeout: 30,
            retries: 3
        )

    fn with_host(self, host: text) -> ServerConfig:
        self.host = host
        return self

# ✅ Implicit static + fluent API
val config = ServerConfig.default()
    .with_host("api.example.com")
```

### Example 4: Multiple Factory Methods

```simple
struct Rectangle:
    width: i64
    height: i64

impl Rectangle:
    fn new(width: i64, height: i64) -> Rectangle:
        return Rectangle(width, height)

    fn square(size: i64) -> Rectangle:
        return Rectangle(size, size)

    fn from_area(area: i64) -> Rectangle:
        val side = sqrt(area) as i64
        return Rectangle(side, side)

# ✅ Implicit static - semantic clarity
val rect = Rectangle.new(10, 20)
val square = Rectangle.square(15)
val area_rect = Rectangle.from_area(100)
```

### Example 5: Test Fixtures (Local Scope)

```simple
fn test_user_creation():
    # Struct defined in test function
    struct TestUser:
        name: text
        age: i64

    # ✅ Direct construction - works in local scope
    val user1 = TestUser(name: "Alice", age: 30)
    val user2 = TestUser(name: "Bob", age: 25)

    # If you need custom logic, use explicit static
    impl TestUser:
        static fn adult(name: text) -> TestUser:
            return TestUser(name: name, age: 18)

    val adult = TestUser.adult("Charlie")
```

### Example 6: From Conversions

```simple
struct Point:
    x: i64
    y: i64

impl Point:
    fn from_tuple(t: (i64, i64)) -> Point:
        return Point(t.0, t.1)

    fn from_array(arr: [i64]) -> Option<Point>:
        if arr.len() >= 2:
            return Some(Point(arr[0], arr[1]))
        else:
            return None

# ✅ Implicit static - idiomatic Rust-like conversions
val p1 = Point.from_tuple((3, 4))
match Point.from_array([10, 20, 30]):
    case Some(p):
        print "Point created: ({p.x}, {p.y})"
    case None:
        print "Array too short"
```

### Example 7: Resource Acquisition

```simple
struct FileHandle:
    path: text
    mode: text

impl FileHandle:
    fn open(path: text, mode: text) -> Result<FileHandle, text>:
        # Attempt to open file
        if file_exists(path) or mode == "w":
            return Ok(FileHandle(path: path, mode: mode))
        else:
            return Err("File not found: {path}")

    fn create(path: text) -> Result<FileHandle, text>:
        return FileHandle.open(path, "w")

# ✅ Implicit static - RAII-style resource acquisition
match FileHandle.open("data.txt", "r"):
    case Ok(handle):
        # Use handle
        print "Opened: {handle.path}"
    case Err(msg):
        print "Error: {msg}"
```

## Pattern Comparison

| Aspect | Direct | Implicit Static | Explicit Static |
|--------|--------|----------------|-----------------|
| **Boilerplate** | None | Low | Medium |
| **Scope Support** | All | Module only | All |
| **Custom Logic** | No | Yes | Yes |
| **Readability** | Excellent | Excellent | Good |
| **Maintainability** | High | High | High |
| **Python-like** | Yes | No | No |
| **Rust-like** | No | Yes | Yes |

## Common Mistakes

### ❌ Mistake 1: Unnecessary wrapper

```simple
# ❌ Bad - pointless wrapper around direct construction
impl Point:
    fn new(x: i64, y: i64) -> Point:
        return Point(x, y)  # Does nothing useful!

val p = Point.new(3, 4)
```

**Fix:**
```simple
# ✅ Good - just use direct construction
val p = Point(3, 4)
```

### ❌ Mistake 2: Using implicit static in local scope

```simple
fn test():
    struct Point: x: i64, y: i64

    impl Point:
        fn new(x: i64, y: i64) -> Point:  # Won't work!
            return Point(x, y)

    val p = Point.new(3, 4)  # ❌ Error: unsupported path call
```

**Fix:**
```simple
fn test():
    struct Point: x: i64, y: i64

    # ✅ Option 1: Direct construction
    val p1 = Point(3, 4)

    # ✅ Option 2: Explicit static
    impl Point:
        static fn new(x: i64, y: i64) -> Point:
            return Point(x, y)
    val p2 = Point.new(3, 4)
```

### ❌ Mistake 3: Forgetting validation

```simple
# ❌ Bad - no validation, allows invalid state
struct Age:
    value: i64

val age = Age(-5)  # Negative age!
```

**Fix:**
```simple
# ✅ Good - validation in constructor
impl Age:
    fn new(value: i64) -> Option<Age>:
        if value >= 0 and value <= 150:
            return Some(Age(value))
        else:
            return None

# Force validation
match Age.new(-5):
    case Some(age): ...
    case None: print "Invalid age"
```

## Best Practices

1. **Default to direct construction** - Only add constructors when you need them
2. **Use implicit static at module level** - Less boilerplate, same clarity
3. **Use explicit static in local scopes** - When implicit doesn't work
4. **Named constructors for semantics** - `from_string()`, `with_capacity()`, etc.
5. **Return Option/Result for fallible constructors** - Don't panic, handle errors
6. **Keep constructors simple** - Complex logic belongs in separate methods
7. **Named parameters for clarity** - When you have 3+ parameters

## Migration from Other Languages

### From Python

```python
# Python - must write __init__
class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y
```

```simple
# Simple - zero boilerplate
struct Point: x: i64, y: i64
val p = Point(3, 4)
```

### From Rust

```rust
// Rust - must write impl
struct Point { x: i64, y: i64 }

impl Point {
    fn new(x: i64, y: i64) -> Self {
        Point { x, y }
    }
}
```

```simple
# Simple - direct construction or implicit static
struct Point: x: i64, y: i64

# Option 1: Direct (recommended)
val p = Point(3, 4)

# Option 2: Custom logic
impl Point:
    fn new(x: i64, y: i64) -> Point:
        return Point(x, y)
```

### From JavaScript

```javascript
// JavaScript - must write constructor
class Point {
    constructor(x, y) {
        this.x = x;
        this.y = y;
    }
}
```

```simple
# Simple - works immediately
struct Point: x: i64, y: i64
val p = Point(3, 4)
```

## Summary

**Simple's constructor philosophy:**
- **Zero boilerplate by default** - Direct construction works out of the box
- **Add constructors when needed** - Validation, defaults, factory methods
- **Implicit static reduces noise** - Auto-recognizes constructor patterns
- **Explicit when needed** - For local scopes or maximum clarity

**Quick reference:**
- Simple data? → `Point(3, 4)`
- Need validation? → `fn new() -> Option<T>`
- Factory methods? → `fn from_*()`, `fn with_*()`
- Local scope? → Use direct or explicit `static`

Choose the pattern that makes your code clearest and most maintainable. When in doubt, start with direct construction and add constructors only when you need custom logic.

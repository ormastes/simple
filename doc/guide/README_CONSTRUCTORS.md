# Constructor Documentation Index

Complete documentation for Simple's constructor system.

## Quick Start

**Want to create objects? Just do it:**
```simple
struct Point:
    x: i64
    y: i64

val p = Point(3, 4)  # That's it!
```

No `__init__`, no `new` method, no boilerplate. Just declare and use.

## Documentation Files

### 1. 🚀 **Start Here**

**[constructors_updated.md](constructors_updated.md)** - Primary reference
- Direct Python-style construction (recommended)
- Optional static constructors with implicit `static`
- Complete examples with validation, builders, factory methods
- Comparison with Python and Rust

**Key takeaway:** Use `Point(3, 4)` for most cases. Add `fn new()` only when you need custom logic.

### 2. 📊 **Language Comparison**

**[constructors_comparison.md](constructors_comparison.md)** - Cross-language comparison
- Side-by-side code examples
- Simple vs Python vs Ruby vs Rust vs JavaScript
- Migration guides from each language
- Philosophy differences

**Key takeaway:** Simple has the cleanest syntax with zero boilerplate, combining Python's ergonomics with Rust's type safety.

### 3. 🎯 **Practical Guide**

**[constructor_patterns_guide.md](constructor_patterns_guide.md)** - Real-world patterns
- When to use each constructor pattern
- Decision tree for choosing the right approach
- 7 real-world examples (DTOs, validation, builders, factories, etc.)
- Common mistakes and fixes
- Best practices

**Key takeaway:** Start with direct construction, add constructors only when needed for validation or factory methods.

### 4. 🔧 **Implementation Details**

**[constructor_implementation_status.md](constructor_implementation_status.md)** - Technical reference
- What works and what doesn't
- Known limitations (local scope issue)
- Parser implementation details
- Test coverage status
- Workarounds for edge cases

**Key takeaway:** Everything works at module level. Use explicit `static` or direct construction in local scopes.

## Three Constructor Patterns

### Pattern 1: Direct Construction (Recommended)

```simple
struct Point: x: i64, y: i64

val p = Point(3, 4)           # ✅ Python-style
val p2 = Point(x: 10, y: 20)  # ✅ Named parameters
```

**Pros:** Zero boilerplate, works everywhere, Python-familiar
**Use when:** You don't need validation or custom logic (most cases)

### Pattern 2: Implicit Static Constructor

```simple
impl Point:
    fn new(x: i64, y: i64) -> Point:  # No 'static' keyword!
        return Point(abs(x), abs(y))  # Add validation

val p = Point.new(-3, 4)  # Becomes Point(3, 4)
```

**Pros:** Less boilerplate, constructor names auto-recognized
**Use when:** You need validation, defaults, or factory methods (at module level)

### Pattern 3: Explicit Static Constructor

```simple
impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x, y)
```

**Pros:** Works everywhere, explicit and clear
**Use when:** You want maximum clarity or need to work in local scopes

## Constructor Names Auto-Recognized

These function names are **automatically static** (no `static` keyword needed):
- `new` - Primary constructor
- `create` - Alternative constructor
- `default` - Zero-argument constructor
- `init` - Initialization constructor
- `from_*` - Conversion constructors (e.g., `from_string`, `from_array`)
- `with_*` - Builder-style constructors (e.g., `with_capacity`, `with_name`)

## Quick Reference Card

| Task | Pattern | Example |
|------|---------|---------|
| Simple data object | Direct | `Point(3, 4)` |
| Named parameters | Direct | `Point(x: 3, y: 4)` |
| With validation | Implicit static | `fn new() -> Option<T>` |
| Factory method | Implicit static | `fn from_string(s: text)` |
| Builder pattern | Implicit static | `fn default()` + `fn with_*()` |
| Local scope | Direct or explicit | `Point(3, 4)` or `static fn new()` |

## Comparison at a Glance

```simple
# Simple - Zero boilerplate
struct Point: x: i64, y: i64
val p = Point(3, 4)
```

```python
# Python - Must write __init__
class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y
p = Point(3, 4)
```

```rust
// Rust - Must write impl
struct Point { x: i64, y: i64 }
impl Point {
    fn new(x: i64, y: i64) -> Self {
        Point { x, y }
    }
}
let p = Point::new(3, 4);
```

**Winner:** Simple - Just declare and use!

## Common Questions

**Q: Do I need to write a constructor?**
A: No! Direct construction `Point(3, 4)` works immediately.

**Q: When should I add a constructor method?**
A: Only when you need validation, defaults, or factory methods.

**Q: Should I use `fn new()` or `static fn new()`?**
A: At module level, `fn new()` is less boilerplate. In local scopes, use `static fn new()`.

**Q: Can I use both direct construction and `new()` methods?**
A: Yes! They coexist perfectly. Users can choose whichever they prefer.

**Q: Why doesn't implicit static work in local scopes?**
A: Technical limitation in method resolution. Use direct construction or explicit `static` as workaround.

**Q: What's the recommended primary pattern?**
A: Direct construction `Point(3, 4)` - zero boilerplate, works everywhere.

## Examples by Use Case

### Data Transfer Objects
```simple
struct UserDTO: id: i64, name: text, email: text
val user = UserDTO(123, "Alice", "alice@example.com")
```

### Validated Types
```simple
impl Age:
    fn new(value: i64) -> Option<Age>:
        if value >= 0 and value <= 150:
            return Some(Age(value))
        return None
```

### Builder Pattern
```simple
impl Config:
    fn default() -> Config:
        return Config("localhost", 8080, 30)

    fn with_host(self, host: text) -> Config:
        self.host = host
        return self

val cfg = Config.default().with_host("api.example.com")
```

### Factory Methods
```simple
impl Rectangle:
    fn square(size: i64) -> Rectangle:
        return Rectangle(size, size)

    fn from_area(area: i64) -> Rectangle:
        val side = sqrt(area) as i64
        return Rectangle(side, side)
```

## See Also

- **Main Language Guide:** `CLAUDE.md` - Quick syntax reference
- **Coding Standards:** `.claude/skills/coding.md` - Full style guide
- **Test Examples:** `test/lib/std/integration/constructor_spec.spl` - Working test suite

## Updates

- **2026-01-22:** Implemented implicit static constructors
- **2026-01-22:** Documented Python-style as primary pattern
- **2026-01-22:** Created comprehensive pattern guide

---

**TL;DR:** Declare struct, use immediately like Python. Add `fn new()` only when you need custom logic. Simple is the only language with truly zero-boilerplate constructors.

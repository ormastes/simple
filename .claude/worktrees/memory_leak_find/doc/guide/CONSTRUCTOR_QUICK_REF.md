# Constructor Quick Reference Card

## The 2-Second Summary

```simple
struct Point: x: i64, y: i64
val p = Point(3, 4)  # That's it!
```

No `__init__`, no `new` method, no boilerplate. Done.

---

## Three Patterns at a Glance

### 🥇 Pattern 1: Direct (Use This!)

```simple
struct Point: x: i64, y: i64

val p = Point(3, 4)
val p2 = Point(x: 10, y: 20)  # Named params
```

**Use when:** Always (unless you need validation)

### 🥈 Pattern 2: Implicit Static

```simple
impl Point:
    fn new(x: i64, y: i64) -> Point:  # No 'static' needed
        return Point(abs(x), abs(y))

val p = Point.new(-3, 4)  # Becomes Point(3, 4)
```

**Use when:** You need validation/defaults (module level only)

### 🥉 Pattern 3: Explicit Static

```simple
impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x, y)
```

**Use when:** Local scopes or you want extra clarity

---

## Decision Tree (30 Seconds)

```
Need custom logic?
NO  → Point(3, 4)
YES → Module level?
      YES → fn new()
      NO  → Point(3, 4) or static fn new()
```

---

## Auto-Recognized Constructor Names

These are **automatically static** (no `static` keyword):

- `fn new()` - Primary constructor
- `fn create()` - Alternative
- `fn default()` - Zero-args
- `fn init()` - Initialization
- `fn from_*()` - Conversions (`from_string`, `from_array`, etc.)
- `fn with_*()` - Builders (`with_capacity`, `with_name`, etc.)

---

## Common Use Cases

### Data Object
```simple
struct User: id: i64, name: text
val user = User(123, "Alice")
```

### Validation
```simple
impl Age:
    fn new(v: i64) -> Option<Age>:
        return Some(Age(v)) if v >= 0 else None
```

### Builder
```simple
impl Config:
    fn default() -> Config:
        return Config("localhost", 8080)

    fn with_host(self, h: text) -> Config:
        self.host = h
        return self

val cfg = Config.default().with_host("api.com")
```

### Factory
```simple
impl Rect:
    fn square(size: i64) -> Rect:
        return Rect(size, size)

val sq = Rect.square(10)
```

---

## Comparison

| Language | Code |
|----------|------|
| **Simple** | `struct Point: x: i64, y: i64`<br>`val p = Point(3, 4)` |
| Python | `class Point:`<br>&nbsp;&nbsp;&nbsp;&nbsp;`def __init__(self, x, y):`<br>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`self.x = x`<br>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`self.y = y`<br>`p = Point(3, 4)` |
| Rust | `struct Point { x: i64, y: i64 }`<br>`impl Point {`<br>&nbsp;&nbsp;&nbsp;&nbsp;`fn new(x: i64, y: i64) -> Self {`<br>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`Point { x, y }`<br>&nbsp;&nbsp;&nbsp;&nbsp;`}`<br>`}`<br>`let p = Point::new(3, 4);` |

**Simple wins:** 3 lines vs 6-8 lines

---

## Common Mistakes ❌ → Fixes ✅

### Mistake 1: Pointless wrapper
```simple
# ❌ Don't do this
impl Point:
    fn new(x: i64, y: i64) -> Point:
        return Point(x, y)  # Adds nothing!

# ✅ Do this
val p = Point(3, 4)  # Direct!
```

### Mistake 2: Implicit static in function
```simple
# ❌ Won't work
fn test():
    struct Point: x: i64, y: i64
    impl Point:
        fn new(x, y) -> Point: ...  # Error!

# ✅ Works
fn test():
    struct Point: x: i64, y: i64
    val p = Point(3, 4)  # Direct!
```

### Mistake 3: Allowing invalid state
```simple
# ❌ Bad - no validation
struct Age: value: i64
val age = Age(-5)  # Negative age!

# ✅ Good - validation
impl Age:
    fn new(v: i64) -> Option<Age>:
        return Some(Age(v)) if v >= 0 else None
```

---

## Pro Tips

1. **Start simple** - Use `Point(3, 4)` until you need more
2. **Validate early** - Return `Option<T>` or `Result<T, E>` from constructors
3. **Named params for clarity** - `Config(host: "localhost", port: 8080)`
4. **Use factory methods** - `Rectangle.square(10)` is clearer than `Rectangle.new(10, 10)`
5. **Keep constructors simple** - Move complex logic to separate methods

---

## One-Liners

- **Zero boilerplate:** Declare struct → use immediately
- **Python syntax:** `Point(3, 4)` works out of the box
- **Smart static:** `fn new()` recognized automatically
- **Three patterns:** Direct (primary), implicit static, explicit static
- **Type safe:** Full static typing like Rust
- **Flexible:** Mix patterns as needed

---

## Learn More

- **Quick start:** `doc/guide/README_CONSTRUCTORS.md`
- **Patterns:** `doc/guide/constructor_patterns_guide.md`
- **Full reference:** `doc/guide/constructors_updated.md`
- **Comparison:** `doc/guide/constructors_comparison.md`

---

**TL;DR:** Type `Point(3, 4)` and you're done. Add `fn new()` only if you need validation. Simple is the only statically-typed language with zero-boilerplate constructors. 🎉

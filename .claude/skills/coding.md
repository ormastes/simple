# Coding Skill - Simple Language Compiler

## Language Rules

### Common Mistakes from Other Languages

Simple provides helpful error messages when you use syntax from other languages. See `doc/guide/common_mistakes.md` for complete guide.

**Quick Reference:**

| From Language | Wrong | Correct Simple |
|--------------|-------|---------------|
| Python | `def foo():` | `fn foo():` |
| Python | `None` | `nil` |
| Python | `True`/`False` | `true`/`false` |
| Python | `self.x` | `x` (self implicit) |
| Rust | `let mut x` | `var x` |
| Rust | `fn(&mut self)` | `me fn()` |
| Rust | `::<T>` | `<T>` |
| Java/C++ | `public class` | `pub class`/`pub struct` |
| Java/C++ | `void foo()` | `fn foo():` (omit return type) |
| Java/C++ | `new Point()` | `Point {}` |
| Java/C++ | `this.x` | `x` (self implicit) |
| TypeScript | `function foo()` | `fn foo():` |
| TypeScript | `const x` | `val x` |
| TypeScript | `interface I` | `trait I:` |

**Error Recovery System:**
- The parser detects common mistakes and provides helpful suggestions
- **Warnings** (not errors) for verbose but valid syntax like explicit return types
- See error messages with examples: `doc/examples/error_messages_demo.spl`

## Language Rules

### String Literals
```simple
# Double-quoted = interpolated (default)
val name = "World"
val greeting = "Hello, {name}!"   # "Hello, World!"
print("Value: {1 + 2}")           # "Value: 3"

# Single-quoted = raw (no interpolation)
val raw = 'No {interpolation} here'

# Triple-quoted = docstring (multi-line)
"""
Multi-line
documentation
"""
```

**DO NOT** use `f"..."` prefix - it's redundant.

### Variable Declarations
```simple
# Immutable variable (default, preferred)
val name = "Alice"
val count = 42
val items = [1, 2, 3]

# Mutable variable (explicit)
var counter = 0
var buffer = []
counter += 1
buffer.append(item)
```

**Rules:**
- Use `val` for immutable variables (preferred, safe default)
- Use `var` for mutable variables (explicit mutation)
- Prefer `val` unless you need to reassign the variable

### Scripts Policy

**ALL scripts must be in Simple (.spl), NOT Python/Bash!**

```simple
# scripts/my_tool.spl
import std.io
import std.fs
import std.args

fn main():
    val args = args.get_args()
    if args.len() < 2:
        io.println("Usage: simple scripts/my_tool.spl <arg>")
        return 1
    io.println("Processing: {args[1]}")
    return 0
```

Run: `./target/debug/simple scripts/my_tool.spl arg1 arg2`

## Coding Standards

### Avoid Over-Engineering
- Only make directly requested changes
- Don't add features beyond what's asked
- Don't refactor surrounding code
- Don't add docstrings/comments to unchanged code
- Don't add error handling for impossible scenarios

### Security
- No command injection, XSS, SQL injection
- Validate at system boundaries only
- Trust internal code and framework guarantees

### Code Style
- Keep solutions simple and focused
- Don't create helpers for one-time operations
- Prefer 3 similar lines over premature abstraction
- Delete unused code completely (no `_vars`, `// removed`)

## Rust Conventions

### Module Structure
```rust
// lib.rs
pub mod feature;
pub use feature::Feature;

// feature.rs
pub struct Feature { ... }

impl Feature {
    pub fn new() -> Self { ... }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_feature() { ... }
}
```

### Error Handling
```rust
use anyhow::{Result, Context};

fn do_something() -> Result<Value> {
    operation().context("failed to do operation")?;
    Ok(value)
}
```

### Logging
```rust
use tracing::{debug, info, warn, error};

#[tracing::instrument]
fn traced_function() {
    info!("operation started");
}
```

## Simple Language Conventions

### Type Names
- **No `Int` type** - use `i32`, `i64`, `u32`, `u64`, etc.
- **No `Float` type** - use `f32` or `f64`
- Use specific-width integer types: `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`

### Contracts
```simple
fn safe_divide(a: i32, b: i32) -> i32:
    in: b != 0, "divisor must be non-zero"
    out(ret): ret * b == a or a % b != 0
    return a / b
```

### Reference Capabilities
- `T` - Shared reference
- `mut T` - Exclusive mutable reference
- `iso T` - Isolated (transferable ownership)

### Method Self Parameter
Simple uses **LL(1)-friendly syntax** with **implicit self**. Use `me` for mutable methods:

```simple
pub struct Counter:
    value: i32

impl Counter:
    # Static method - no self access
    static fn new() -> Counter:
        return Counter(value: 0)

    # Immutable method - self is implicit
    fn get_value() -> i32:
        return self.value

    # Mutable method - use 'me' keyword
    me increment():
        self.value += 1

    # Mutable method with parameters
    me add(amount: i32):
        self.value += amount

    # Immutable method with parameters
    fn is_greater_than(other: i32) -> bool:
        return self.value > other
```

**Rules:**
- `static fn` - Static/associated function, no self access
- `fn` - Immutable method, self implicit (read-only)
- `me` - Mutable method, self implicit (mutable)
- In method bodies, use `self.field` to access fields

**Quick Reference:**
```simple
# Static methods (no self)
static fn new() -> Counter:                  # ✓ Static constructor
static fn from_value(val: i32) -> Counter:  # ✓ Static factory

# Instance methods (self IMPLICIT)
fn getter() -> i32:                          # ✓ Read-only instance method
me setter(val: i32):                         # ✓ Mutable instance method
fn query() -> bool:                          # ✓ Read-only check
me modify():                                 # ✓ Mutates the instance
```

**Important:** `self` is implicit in signatures but explicit in method bodies.

```simple
pub struct Point:
    x: f64
    y: f64

impl Point:
    # Static method - no self, called as Point::new()
    static fn new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable method - self implicit, called as point.get_x()
    fn get_x() -> f64:
        return self.x

    # Mutable method - self implicit, called as point.set_x(5.0)
    me set_x(value: f64):
        self.x = value

    # Immutable method - self implicit, called as point.distance_to(other)
    fn distance_to(other: Point) -> f64:
        val dx = self.x - other.x
        val dy = self.y - other.y
        return (dx * dx + dy * dy).sqrt()

    # Mutable method - self implicit, called as point.translate(10.0, 20.0)
    me translate(dx: f64, dy: f64):
        self.x += dx
        self.y += dy
```

**Summary:**
- **Static method:** `static fn method(...)` (no self)
- **Instance method (read-only):** `fn method(...)` (self implicit)
- **Instance method (mutable):** `me method(...)` (self implicit)

### Function Visibility
- Functions are **public by default**
- Prefix with underscore (`_`) for private functions
- **Do NOT use `pub fn`** - just use `fn` (public is default)

```simple
# Public function (default)
fn calculate(x: i32) -> i32:
    return _helper(x) * 2

# Private function (underscore prefix)
fn _helper(x: i32) -> i32:
    return x + 1
```

### Effect Decorators
```simple
@pure       # No side effects
@io         # Console I/O
@fs         # File system
@net        # Network
@unsafe     # Unsafe operations
```

## Bug Reports

File in `simple/bug_report.md`:
```markdown
### [Component] Brief description
**Type:** Bug
**Priority:** High | Medium | Low
**Description:** ...
**Expected:** ...
**Actual:** ...
**Reproduction:** ...
```

## See Also

- **`doc/guide/common_mistakes.md`** - Complete guide for transitioning from other languages
- **`doc/guide/coding_style.md`** - Full coding style guide (domain types, defaults, config, AOP)
- `doc/examples/error_messages_demo.spl` - Demo file showing all error types
- `doc/spec/syntax.md` - Lexical structure
- `doc/spec/types.md` - Type system
- `doc/spec/functions.md` - Functions, pattern matching
- `doc/research/api_design_index.md` - API guidelines

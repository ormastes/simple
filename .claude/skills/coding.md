# Coding Skill - Simple Language Compiler

## Language Rules

### String Literals
```simple
# Double-quoted = interpolated (default)
let name = "World"
let greeting = "Hello, {name}!"   # "Hello, World!"
print("Value: {1 + 2}")           # "Value: 3"

# Single-quoted = raw (no interpolation)
let raw = 'No {interpolation} here'

# Triple-quoted = docstring (multi-line)
"""
Multi-line
documentation
"""
```

**DO NOT** use `f"..."` prefix - it's redundant.

### Scripts Policy

**ALL scripts must be in Simple (.spl), NOT Python/Bash!**

```simple
# scripts/my_tool.spl
import std.io
import std.fs
import std.args

fn main():
    let args = args.get_args()
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

- **`doc/guide/coding_style.md`** - Full coding style guide (domain types, defaults, config, AOP)
- `doc/spec/syntax.md` - Lexical structure
- `doc/spec/types.md` - Type system
- `doc/spec/functions.md` - Functions, pattern matching
- `doc/research/api_design_index.md` - API guidelines

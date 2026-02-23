# Simple Standard Library API Design

**Note:** This file has been reorganized for better maintainability.

## Overview

Comprehensive API design guidelines based on lessons learned from:
- **Rust**: Zero-cost abstractions, explicit error handling
- **Python**: Readability, batteries included
- **Ruby**: Developer happiness, expressive syntax
- **Scala**: Functional programming patterns
- **Go**: Simplicity, explicit error handling
- **Java**: What *not* to do (API design regrets)

## Documentation Structure

See **[API Design Index](api_design_index.md)** for detailed guidelines organized by topic.

## Quick Reference

### Core Design Principles

1. **Explicit over Implicit**
   - No hidden panics (`expect(msg)` not `unwrap()`)
   - Clear error propagation (`?` operator, Result types)
   - Explicit conversions (`to_*` for allocating, `as_*` for borrowing)

2. **Consistent Naming Conventions**
   ```simple
   to_*()      # Convert with allocation (to_string, to_vec)
   as_*()      # Zero-cost view (as_str, as_bytes)
   into_*()    # Consume self (into_iter, into_string)
   from_*()    # Constructor (from_bytes, from_utf8)
   try_*()     # Fallible version (try_from, try_into)
   is_*()      # Boolean predicate (is_empty, is_sorted)
   has_*()     # Ownership query (has_value, has_error)
   ```

3. **Safe by Default**
   - Bounds-checked by default
   - Unsafe operations explicitly marked
   - Opt-in performance with `_unchecked` suffixes

4. **Ergonomic Iteration**
   - Both functional (`map`, `filter`, `fold`) and imperative (`each`, `each_with_index`)
   - Ruby-style blocks for common patterns
   - Python-style comprehensions

5. **Zero-Cost Abstractions**
   - High-level APIs compile to efficient code
   - Inline-friendly small methods
   - Monomorphization for generics

### Common Patterns

#### Option/Result Handling
```simple
# Error handling
let value = opt.expect("user must be logged in")  # Explicit panic message
let value = opt.unwrap_or(default)                # Provide fallback
let value = result?                                # Early return on error

# Safe access
items.get(i)              # Option[T]
items.get_unchecked(i)    # T, unsafe
```

#### Iteration
```simple
# Functional style
items.map(x => x * 2).filter(x => x > 10).sum()

# Ruby style
items.each do |x|
    print(x)

# Python style
[x * 2 for x in items if x > 10]
```

#### Conversion
```simple
let s: String = "hello"
let view: &str = s.as_str()      # Borrow
let owned: String = view.to_string()  # Allocate
let consumed: Vec[u8] = s.into_bytes()  # Move
```

#### Builder Pattern
```simple
let req = HttpRequest.builder()
    .method(GET)
    .url("https://api.example.com")
    .header("Accept", "application/json")
    .timeout(30_s)
    .build()?
```

## Implementation Status

| Category | Status | Notes |
|----------|--------|-------|
| **Option/Result API** | ✅ Defined | Core error handling patterns |
| **Naming Conventions** | ✅ Defined | Consistent across stdlib |
| **Collections API** | 📋 Designed | Array, dict, set patterns |
| **String API** | 📋 Designed | UTF-8 handling, formatting |
| **Numeric API** | 📋 Designed | Math, conversions, suffixes |
| **Error Handling** | ✅ Implemented | Result, ?, expect |
| **I/O API** | 🔄 In Progress | File, network, async |
| **Concurrency API** | ✅ Implemented | Actors, async, channels |
| **Testing API** | ✅ Implemented | BDD spec, doctest |
| **Documentation** | �� Designed | Docstring standards |

## Key Lessons from Other Languages

### From Rust
✅ **Adopt:**
- `Result<T, E>` for error handling
- `Option<T>` instead of null
- Clear `to_*`/`as_*`/`into_*` naming
- Trait-based abstractions

❌ **Avoid:**
- `unwrap()` without message - use `expect(msg)` only
- Over-complicated type signatures
- Excessive lifetime annotations

### From Python
✅ **Adopt:**
- List/dict comprehensions
- Multiple return unpacking
- `with` context managers
- Operator overloading for clarity

❌ **Avoid:**
- Implicit type coercion
- Mutable default arguments
- Global namespace pollution

### From Ruby
✅ **Adopt:**
- Block syntax for iteration
- `each`, `map`, `select` naming
- `is_*` prefix for predicates (NOT `?` suffix - see note below)
- Symbol/keyword arguments

> **Design Decision:** Simple does NOT support `?` in method names (unlike Ruby).
> The `?` character is reserved for:
> - Try operator: `result?` (error propagation, like Rust)
> - Optional types: `T?` (sugar for `Option<T>`)
> - Future: Optional chaining `?.` and nullish coalescing `??`
>
> Use `is_*` prefix instead: `is_empty()`, `is_valid()`, `is_some()`

❌ **Avoid:**
- Too much magic (method_missing)
- Monkey patching core classes
- Implicit returns everywhere

### From Scala
✅ **Adopt:**
- For-comprehensions (desugared to map/flatMap)
- Pattern matching
- Implicit type classes (traits)

❌ **Avoid:**
- Over-abstraction
- Too many operators
- Complex implicits

### From Go
✅ **Adopt:**
- Explicit error handling
- Simple concurrency primitives
- Clear naming (no abbreviations)

❌ **Avoid:**
- `err != nil` repetition (use `?` operator)
- No generics (we have them!)
- Interface{} type erasure

### From Java
❌ **Avoid Everything:**
- Checked exceptions
- `getX()` / `setX()` verbosity
- `AbstractFactoryBean` naming
- Null pointer exceptions

## Design Process

When designing new stdlib APIs:

1. **Start with use cases** - Write example code first
2. **Check existing art** - Review Rust, Python, Ruby equivalents
3. **Follow naming conventions** - Consistent prefixes/suffixes
4. **Provide both styles** - Functional and imperative where appropriate
5. **Add comprehensive docs** - Docstrings with `>>>` examples
6. **Write BDD specs** - Cover common and edge cases
7. **Benchmark critical paths** - Ensure zero-cost abstractions

## See Also

- **[API Design Index](api_design_index.md)** - Detailed guidelines by topic
- **[Standard Library Spec](../spec/stdlib.md)** - Complete stdlib specification
- **[Unit Types Spec](../spec/units.md)** - Semantic type system
- **[Testing Guide](../guides/test.md)** - How to test stdlib APIs
- **[Architecture](../architecture/overview.md)** - Module organization

---

**Full detailed guidelines available in: [API Design Index](api_design_index.md)**

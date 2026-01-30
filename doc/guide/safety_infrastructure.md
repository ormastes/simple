# Safety Infrastructure Guide

This guide explains how to use the Simple compiler's safety infrastructure to prevent common bug patterns.

## Overview

The safety infrastructure provides safe alternatives to common unsafe Rust patterns:

1. **Checked Arithmetic** - Prevent integer overflow/underflow
2. **Safe Type Conversions** - Explicit overflow handling
3. **Safe Array Indexing** - Bounds checking with good error messages
4. **Safe Mutex Operations** - Better error messages for poisoned locks
5. **Safe String Operations** - UTF-8 aware operations

## Usage

### 1. Checked Arithmetic

**Problem:** Integer overflow causes silent wraparound or panics.

```rust
// ❌ BAD - Can overflow silently in release mode
let result = a + b;

// ❌ BAD - Panics in debug, wraps in release
let size = width * height;

// ✅ GOOD - Explicit overflow handling
use simple_common::{safe_add, safe_mul};

let result = safe_add(a, b)?;
let size = safe_mul(width, height)?;

// ✅ GOOD - Using macro
use simple_common::safe_op;

let result = safe_op!(a + b)?;
let size = safe_op!(width * height)?;
```

**Error Messages:**

```rust
let result = safe_add(i32::MAX, 1);
// Error: "arithmetic overflow: 2147483647 + 1"
```

### 2. Safe Type Conversions

**Problem:** Casting with `as` can silently truncate or overflow.

```rust
// ❌ BAD - Silent truncation
let index = big_number as usize;
let count = negative_number as u32;  // Wraps to huge number!

// ✅ GOOD - Explicit conversion with error handling
use simple_common::{to_usize, to_u32};

let index = to_usize(big_number)?;
let count = to_u32(negative_number)?;  // Error: cannot convert negative
```

**Available Conversions:**

- `to_usize()` - Convert to usize
- `to_i64()` - Convert to i64
- `to_u64()` - Convert to u64
- `to_i32()` - Convert to i32
- `to_u32()` - Convert to u32

**Error Messages:**

```rust
let result = to_usize(-1i32);
// Error: "cannot convert negative value -1 to unsigned type"

let result = to_i32(5_000_000_000i64);
// Error: "conversion overflow: 5000000000 (i64) does not fit in i32"
```

### 3. Safe Array Indexing

**Problem:** Indexing with `[]` panics on out-of-bounds.

```rust
// ❌ BAD - Panics with generic message
let value = arr[index];

// ✅ GOOD - Descriptive error
use simple_common::safe_index;

let value = safe_index(&arr, index)?;

// ✅ GOOD - Using macro
use simple_common::safe_idx;

let value = safe_idx!(arr, index)?;
```

**Negative Indexing (Python-style):**

```rust
use simple_common::safe_index_signed;

let arr = [1, 2, 3, 4, 5];

let last = safe_index_signed(&arr, -1)?;    // 5
let second_last = safe_index_signed(&arr, -2)?;  // 4
```

**Error Messages:**

```rust
let result = safe_index(&arr, 10);
// Error: "index out of bounds: index is 10 but length is 5"

let result = safe_index_signed(&arr, -10);
// Error: "negative index out of bounds: index is -10 but length is 5"
```

### 4. Safe Mutex Operations

**Problem:** `.lock().unwrap()` panics with generic message when poisoned.

```rust
// ❌ BAD - Generic panic message
let guard = mutex.lock().unwrap();

// ✅ GOOD - Descriptive context
use simple_common::safe_lock;

let guard = safe_lock(&mutex, "accessing user cache");

// ✅ GOOD - Using macro
use simple_common::safe_mutex_lock;

let guard = safe_mutex_lock!(mutex, "incrementing counter");
```

**Custom Error Handling:**

```rust
use simple_common::try_lock;

let guard = try_lock(&mutex, "database transaction", |msg| {
    CompileError::internal(msg)
})?;
```

### 5. Safe String Operations

**Problem:** Byte indexing can break UTF-8 boundaries.

```rust
// ❌ BAD - Byte indexing (wrong for UTF-8)
let c = s.as_bytes()[i] as char;  // Breaks on multi-byte chars

// ✅ GOOD - Character indexing
use simple_common::safe_char_at;

let c = safe_char_at(s, i)?;
```

**Substring Extraction:**

```rust
use simple_common::safe_substring;

let s = "Hello 🌍 World";
let hello = safe_substring(s, 0, 5)?;  // "Hello"
let emoji = safe_substring(s, 6, 7)?;  // "🌍"
```

**Error Messages:**

```rust
let result = safe_char_at("Hello", 10);
// Error: "character index 10 out of bounds (length: 5)"
```

## Migration Guide

### Step 1: Find Dangerous Patterns

Search for these patterns in your code:

```bash
# Integer arithmetic
grep -r "as usize" src/
grep -r "as i32" src/
grep -r "as u64" src/

# Array indexing
grep -r "\[.*\]" src/ | grep -v "//.*\["

# Unwraps
grep -r "\.unwrap()" src/ | grep -v "test"
grep -r "\.lock().unwrap()" src/
```

### Step 2: Replace with Safe Alternatives

**Example 1: Array Indexing**

```rust
// Before
fn get_value(arr: &[i32], idx: usize) -> i32 {
    arr[idx]  // Can panic
}

// After
use simple_common::safe_index;

fn get_value(arr: &[i32], idx: usize) -> Result<i32, IndexError> {
    Ok(*safe_index(arr, idx)?)
}
```

**Example 2: Type Conversions**

```rust
// Before
fn compute_size(width: i64, height: i64) -> usize {
    (width * height) as usize  // Can overflow twice!
}

// After
use simple_common::{safe_mul, to_usize};

fn compute_size(width: i64, height: i64) -> Result<usize, ArithmeticError> {
    let area = safe_mul(width, height)?;
    to_usize(area).map_err(|e| ArithmeticError::Overflow {
        op: "convert",
        a: area.to_string(),
        b: "usize".to_string(),
    })
}
```

**Example 3: Arithmetic**

```rust
// Before
fn add_offset(base: usize, offset: i64) -> usize {
    if offset >= 0 {
        base + offset as usize
    } else {
        base - (-offset) as usize
    }
}

// After
use simple_common::{safe_add, safe_sub, to_usize};

fn add_offset(base: usize, offset: i64) -> Result<usize, ArithmeticError> {
    if offset >= 0 {
        safe_add(base, to_usize(offset)?)
    } else {
        safe_sub(base, to_usize(-offset)?)
    }
}
```

### Step 3: Update Error Handling

The safety functions return `Result` types, so you need to handle errors:

```rust
// Option 1: Propagate with ?
fn process(arr: &[i32], idx: usize) -> Result<i32, IndexError> {
    let value = safe_index(arr, idx)?;
    Ok(*value * 2)
}

// Option 2: Provide default
fn process_with_default(arr: &[i32], idx: usize) -> i32 {
    safe_index(arr, idx).map(|v| *v * 2).unwrap_or(0)
}

// Option 3: Convert to Option
fn process_optional(arr: &[i32], idx: usize) -> Option<i32> {
    safe_index(arr, idx).ok().map(|v| *v * 2)
}

// Option 4: Map to custom error
fn process_custom(arr: &[i32], idx: usize) -> Result<i32, CompileError> {
    let value = safe_index(arr, idx)
        .map_err(|e| CompileError::internal(e.to_string()))?;
    Ok(*value * 2)
}
```

## Best Practices

### When to Use Safety Infrastructure

**Always Use:**
- User input processing (indices, sizes, counts)
- Array/slice indexing with runtime values
- Type conversions from larger to smaller types
- Arithmetic involving user data or file sizes

**Consider Using:**
- Arithmetic in loops (can accumulate)
- Conversions from signed to unsigned
- String indexing with UTF-8 strings

**Not Needed:**
- Constants and literals (`arr[0]`, `10 + 20`)
- Test code (panics are acceptable)
- When checked at a higher level

### Performance Considerations

The safety functions have minimal overhead:

- **Checked arithmetic**: ~1-2 CPU cycles (same as debug mode)
- **Safe indexing**: Zero overhead (`.get()` is optimized same as `[]`)
- **Type conversions**: Zero overhead (compiler optimizes away)
- **String operations**: O(n) for character indexing (same as `.chars().nth()`)

For hot paths with proven bounds, you can keep unsafe code with a comment:

```rust
// SAFETY: index is guaranteed to be < arr.len() by the loop bounds
let value = arr[index];
```

## Error Types Reference

### ArithmeticError

```rust
pub enum ArithmeticError {
    Overflow { op: &'static str, a: String, b: String },
    Underflow { op: &'static str, a: String, b: String },
    DivisionByZero { dividend: String },
}
```

### ConversionError

```rust
pub enum ConversionError {
    Overflow { from: String, to: &'static str, value: String },
    NegativeToUnsigned { value: String },
}
```

### IndexError

```rust
pub enum IndexError {
    OutOfBounds { index: usize, len: usize },
    NegativeIndex { index: i64, len: usize },
}
```

### StringError

```rust
pub enum StringError {
    InvalidUtf8Boundary { byte_index: usize },
    IndexOutOfBounds { char_index: usize, char_count: usize },
}
```

## Testing

The safety infrastructure includes comprehensive tests:

```bash
# Run safety tests
cargo test -p simple-common safety

# Run all tests
cargo test --workspace
```

## Examples

See `src/rust/common/src/safety.rs` for complete examples and test cases.

## Future Enhancements

Planned improvements:

- [ ] SIMD-accelerated bounds checking
- [ ] Safe pointer arithmetic
- [ ] Safe FFI wrappers
- [ ] Compile-time overflow detection (const generics)
- [ ] Integration with Simple's effect system

## References

- [Rust overflow documentation](https://doc.rust-lang.org/reference/expressions/operator-expr.html#overflow)
- [Clippy overflow lints](https://rust-lang.github.io/rust-clippy/master/index.html#integer_arithmetic)
- Simple compiler safety audit: `doc/report/safety_audit_2026-01-30.md`

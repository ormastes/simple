# Constructor Update - January 22, 2026

## Summary

Completed comprehensive update to Simple's constructor system with three main improvements:

1. ✅ **Documentation Updated** - Python-style `Type(args)` now clearly documented as PRIMARY method
2. ✅ **Implicit Static Feature** - Parser auto-recognizes constructor names (`new`, `create`, `from_*`, etc.)
3. ✅ **Comprehensive Testing** - 10/10 tests passing at module level

## Changes Made

### 1. Documentation Updates

**Files Updated:**
- `CLAUDE.md` - Added constructor quick reference showing Python-style as primary
- `doc/guide/constructors_updated.md` - Updated to emphasize Python-style and implicit static
- `doc/guide/constructors_comparison.md` - Already comprehensive, no changes needed
- `doc/guide/constructor_implementation_status.md` - **NEW** - Detailed implementation status and limitations

### 2. Parser Implementation

**File:** `src/rust/parser/src/types_def/trait_impl_parsing.rs`

Added helper function:
```rust
fn is_constructor_name(name: &str) -> bool {
    matches!(name, "new" | "create" | "default" | "init")
        || name.starts_with("from_")
        || name.starts_with("with_")
}
```

Modified impl block parsing (lines 239-243):
```rust
// Implicit static: constructor-like names are automatically static
if !is_static && is_constructor_name(&f.name) {
    is_static = true;
}
```

This prevents `self` parameter injection for constructor-named functions, making them effectively static.

### 3. Test Suite

**File:** `test/lib/std/integration/constructor_spec.spl` - **NEW**

Comprehensive test coverage (10 tests, all passing):
- ✅ Direct construction (primary method)
- ✅ Direct construction with named parameters
- ✅ `fn new()` implicit static
- ✅ `fn create()` implicit static
- ✅ `fn default()` implicit static
- ✅ `fn from_*()` implicit static
- ✅ `fn with_*()` implicit static
- ✅ Explicit `static fn new()` still works
- ✅ Instance methods get implicit `self`
- ✅ Direct and `new()` can coexist

## Implementation Status

### ✅ Fully Working

1. **Direct Python-style construction** - Works everywhere (module + local scope)
   ```simple
   val p = Point(3, 4)
   val p2 = Point(x: 10, y: 20)
   ```

2. **Explicit static methods** - Works at module level
   ```simple
   impl Point:
       static fn new(x: i64, y: i64) -> Point:
           return Point(x, y)
   ```

3. **Implicit static constructors** - Works at module level
   ```simple
   impl Point:
       fn new(x: i64, y: i64) -> Point:  # No 'static' needed!
           return Point(x, y)
   ```

### ⚠️ Known Limitation

**Local Scope Issue:** Implicit static methods don't work when structs are defined inside functions.

**Why:** The interpreter resolves `Type.method()` calls by checking global `impl_methods` map, but locally-defined impls aren't registered there.

**Workaround:** Use direct construction or explicit `static` keyword in local scopes.

**Example:**
```simple
fn test():
    struct Point: x: i64, y: i64

    # ✅ This works
    val p1 = Point(3, 4)

    # ✅ This also works
    impl Point:
        static fn new(x: i64, y: i64) -> Point:
            return Point(x, y)

    # ❌ This doesn't work yet
    impl Point:
        fn new(x: i64, y: i64) -> Point:
            return Point(x, y)
```

## Recommendations for Users

### Best Practices

1. **Use Python-style as PRIMARY:**
   ```simple
   val p = Point(3, 4)  # Recommended
   ```

2. **Use `fn new()` without `static` at module level:**
   ```simple
   impl Point:
       fn new(x: i64, y: i64) -> Point:  # Works at module level
           return Point(x, y)
   ```

3. **Use explicit `static` for clarity or in local scopes:**
   ```simple
   impl Point:
       static fn new(x: i64, y: i64) -> Point:  # Always clear
           return Point(x, y)
   ```

4. **Use named constructors for semantic clarity:**
   ```simple
   impl Rectangle:
       static fn square(size: i64) -> Rectangle:
           return Rectangle(size, size)
   ```

## Comparison with Other Languages

| Feature | Simple | Python | Rust | Ruby | JavaScript |
|---------|--------|--------|------|------|------------|
| **Auto constructor** | ✅ Yes | ❌ No | ❌ No | ❌ No | ❌ No |
| **Call syntax** | `Type(args)` | `Type(args)` | `Type::new()` | `Type.new()` | `new Type()` |
| **Named params** | ✅ Yes | ✅ Yes | ❌ No | ✅ Partial | ❌ No |
| **Implicit static** | ✅ Yes | N/A | ❌ No | N/A | N/A |
| **Boilerplate** | **Zero** | Medium | Medium | Medium | Medium |

## Build and Test Results

**Build:** ✅ Success (46.86s)
```
Finished `release` profile [optimized] target(s) in 46.86s
```

**Tests:** ✅ 10/10 passing
```
Module-Level Constructors
  ✓ Direct construction works (PRIMARY METHOD)
  ✓ Direct construction with named parameters
  ✓ fn new() is implicitly static at module level
  ✓ fn create() is implicitly static
  ✓ fn default() is implicitly static
  ✓ fn from_* is implicitly static
  ✓ fn with_* is implicitly static
  ✓ Explicit static keyword still works
  ✓ Instance methods still get implicit self
  ✓ Direct construction and new() can coexist

10 examples, 0 failures
```

## Future Work

- [ ] Fix local scope method resolution for `Type.method()` calls
- [ ] Extend implicit static to other method naming conventions (if requested)
- [ ] Add compiler warnings for common mistakes (e.g., `fn new()` with `self` parameter)

## Conclusion

Simple now has three working constructor patterns, with Python-style direct construction as the recommended primary approach. The implicit static feature successfully reduces boilerplate at module level, while the existing explicit patterns remain fully supported for clarity and compatibility.

**Key Achievement:** Zero-boilerplate constructors that "just work" - declare a struct, use it immediately like Python, with full static typing like Rust.

---

**Date:** January 22, 2026
**Status:** ✅ Complete (with documented limitations)
**Tests:** 10/10 passing
**Documentation:** Updated and comprehensive

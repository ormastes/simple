# Constructor Implementation Status

## Summary

Simple supports **three constructor patterns**, with varying levels of implementation:

1. ✅ **Direct Python-style construction** - `Point(3, 4)` - **FULLY WORKING**
2. ✅ **Static method with explicit `static`** - `static fn new()` - **FULLY WORKING**
3. ⚠️ **Implicit static for `new()`** - `fn new()` without `static` keyword - **PARSER IMPLEMENTED, RUNTIME PARTIAL**

## What Works

### 1. Direct Construction (Recommended) ✅

```simple
struct Point:
    x: i64
    y: i64

# Works everywhere - module level and function level
val p = Point(3, 4)
val p2 = Point(x: 10, y: 20)  # Named parameters
```

**Status:** ✅ Fully implemented and working
**Scope:** Works at both module level and local function scope

### 2. Explicit Static Methods ✅

```simple
impl Point:
    static fn new(x: i64, y: i64) -> Point:
        return Point(x, y)

    static fn origin() -> Point:
        return Point(0, 0)

# Module level - works
val p1 = Point.new(3, 4)
val p2 = Point.origin()
```

**Status:** ✅ Fully implemented and working
**Scope:** Works at module level only (see limitations below)

### 3. Implicit Static Constructors ⚠️

```simple
impl Point:
    fn new(x: i64, y: i64) -> Point:    # No 'static' keyword
        return Point(x, y)

    fn from_tuple(t: (i64, i64)) -> Point:
        return Point(t.0, t.1)

# Works at module level
val p = Point.new(3, 4)
```

**Status:** ⚠️ Partially implemented
- ✅ Parser recognizes constructor names (`new`, `create`, `default`, `from_*`, `with_*`)
- ✅ Parser automatically treats them as static (no `self` parameter injected)
- ✅ Works at module level
- ❌ Does NOT work in local function scope (known limitation)

**Constructor names that are implicitly static:**
- `new`
- `create`
- `default`
- `init`
- Anything starting with `from_` (e.g., `from_string`, `from_array`)
- Anything starting with `with_` (e.g., `with_capacity`, `with_name`)

## Current Limitations

### Local Scope Issue

**Problem:** Implicit static methods don't work when structs are defined inside functions:

```simple
fn test():
    struct Point:
        x: i64
        y: i64

    impl Point:
        fn new(x: i64, y: i64) -> Point:  # Implicitly static
            return Point(x, y)

    val p = Point.new(3, 4)  # ❌ Error: "unsupported path call"
```

**Workaround:** Use direct construction or explicit `static` keyword:

```simple
fn test():
    struct Point:
        x: i64
        y: i64

    # Option 1: Direct construction (recommended)
    val p1 = Point(3, 4)  # ✅ Works!

    # Option 2: Explicit static
    impl Point:
        static fn new(x: i64, y: i64) -> Point:
            return Point(x, y)

    val p2 = Point.new(3, 4)  # ✅ Works!
```

### Why This Happens

The issue is in how the interpreter resolves method calls:

1. At **module level**: `impl Point` methods are registered in `impl_methods` global map
2. In **local scope**: Structs and impls are defined locally, but the method resolution for `Type.method()` calls only checks the global `impl_methods` map

This is a known limitation that will be addressed in a future update.

## Best Practices

### ✅ Recommended Patterns

1. **Use direct construction as primary pattern:**
   ```simple
   val p = Point(3, 4)  # ✅ Best - works everywhere
   ```

2. **Use explicit `static` for clarity:**
   ```simple
   impl Point:
       static fn new(x: i64, y: i64) -> Point:  # ✅ Clear and works
           return Point(x, y)
   ```

3. **Use named constructors for semantics:**
   ```simple
   impl Rectangle:
       static fn square(size: i64) -> Rectangle:
           return Rectangle(size, size)
   ```

### ❌ Avoid (Until Fixed)

1. **Implicit static in local scopes:**
   ```simple
   fn test():
       struct Point: ...
       impl Point:
           fn new() -> Point: ...  # ❌ Won't work in local scope
   ```

## Testing Status

| Test Case | Status |
|-----------|--------|
| Direct construction (module level) | ✅ Pass |
| Direct construction (local scope) | ✅ Pass |
| Explicit `static fn new()` (module level) | ✅ Pass |
| Explicit `static fn new()` (local scope) | ⚠️ Partial (requires workaround) |
| Implicit `fn new()` (module level) | ✅ Pass |
| Implicit `fn new()` (local scope) | ❌ Fail (known issue) |

## Implementation Details

### Parser Changes

**File:** `src/rust/parser/src/types_def/trait_impl_parsing.rs`

```rust
// Helper function to detect constructor names
fn is_constructor_name(name: &str) -> bool {
    matches!(name, "new" | "create" | "default" | "init")
        || name.starts_with("from_")
        || name.starts_with("with_")
}

// In impl block parsing:
if !is_static && is_constructor_name(&f.name) {
    is_static = true;  // Auto-mark as static
}

// Skip self injection for static methods
if !is_static && (f.params.is_empty() || f.params[0].name != "self") {
    // Inject self parameter for instance methods only
}
```

### Runtime Resolution

**File:** `src/rust/compiler/src/interpreter_call/mod.rs:198-210`

The interpreter resolves `Type.method()` calls by:

1. Checking `impl_methods.get(type_name)` for impl block methods
2. Checking `classes.get(type_name).methods` for class methods
3. Calling method without `self` argument (static call)

**Current gap:** Local scope type registrations don't propagate to these lookups.

## Future Work

- [ ] Fix local scope method resolution for `Type.method()` calls
- [ ] Add comprehensive test suite once local scope is fixed
- [ ] Consider making `new` implicitly static in language spec

## Migration Guide

If you're writing code now:

**Module-level code (works):**
```simple
struct Point: x: i64, y: i64

impl Point:
    fn new(x: i64, y: i64) -> Point:  # Implicit static works!
        return Point(x, y)

val p = Point.new(3, 4)  # ✅ Works
```

**Function-level code (use workarounds):**
```simple
fn my_function():
    struct Point: x: i64, y: i64

    # Option 1: Direct construction (recommended)
    val p1 = Point(3, 4)  # ✅ Works

    # Option 2: Explicit static
    impl Point:
        static fn new(x: i64, y: i64) -> Point:
            return Point(x, y)
    val p2 = Point.new(3, 4)  # ✅ Works
```

## Conclusion

✅ **Python-style direct construction** is the **recommended primary pattern** and works everywhere.

✅ **Explicit `static fn new()`** works reliably at module level.

⚠️ **Implicit `fn new()`** is implemented in the parser but has runtime limitations in local scopes. Use explicit `static` or direct construction as workarounds.

The implicit static feature is a quality-of-life improvement that reduces boilerplate at module level, but the classic patterns remain the most robust choices until the local scope issue is resolved.

# Parser Limitation: Nested Generic Parameters - 2026-01-12

## ✅ RESOLVED (2026-01-18)

**Status:** Nested generics now fully work. The parser correctly handles:
- 2-level nesting: `Option<Guard<T>>`
- 3-level nesting: `Option<Result<List<T>, E>>`
- `>>` token splitting for `List<List<i32>>`
- Struct fields with nested generics
- Function parameters with nested generics

The `synchronization.spl` module loads and parses correctly with all `try_lock()`, `try_read()`, `try_write()` methods.

---

## Historical Context (Original Report)

The Simple language parser previously did not support nested generic type parameters in return types (e.g., `Option<MutexGuard<T>>`). This blocked the implementation of several core concurrency primitives in `sync.spl`.

## Issue

**Problem**: Parser fails to parse return types with nested generic parameters.

**Error Message**: `parse error: Unexpected token: expected Comma, found Colon`

### Minimal Reproduction

```simple
class Guard<T>:
    value: T

fn test() -> Option<Guard<i32>>:
    return nil
```

**Result**: Parse error at line with `Option<Guard<i32>>`

### Affected Files

**`simple/std_lib/src/core/sync.spl`**:
- Line 147: `fn try_lock() -> Option<MutexGuard<T>>:`
- Line 223: `fn try_read() -> Option<RwLockReadGuard<T>>:`
- Line 243: `fn try_write() -> Option<RwLockWriteGuard<T>>:`

## Root Cause

The parser interprets the `>` in `Guard<T>>` as closing the `Option<` rather than understanding it's part of the nested type. This is likely due to:

1. **Greedy `>` matching**: Parser matches the first `>` it sees as the closing bracket for `Option<`
2. **No lookahead for nested generics**: Parser doesn't look ahead to determine if `>` closes inner or outer generic
3. **Ambiguity with shift operator**: `>>` is also the right-shift operator, creating parsing ambiguity

## Workarounds

### Workaround 1: Type Aliases (Works!)

```simple
class Guard<T>:
    value: T

type GuardI32 = Guard<i32>

fn test() -> Option<GuardI32>:  # This parses correctly
    return nil
```

**Limitation**: Requires concrete type instantiation, doesn't work for methods in generic classes.

### Workaround 2: Wrapper Types

```simple
class OptionalMutexGuard<T>:
    guard: Option<MutexGuard<T>>

fn try_lock() -> OptionalMutexGuard<T>:
    # Implementation
```

**Limitation**: Adds boilerplate and reduces API ergonomics.

### Workaround 3: Restructure API

```simple
# Instead of returning Option<Guard<T>>
fn try_lock() -> MutexGuard<T>:
    # Throws error if lock not acquired

# Or use sentinel values
fn try_lock() -> MutexGuard<T>:
    # Returns empty guard if failed
```

**Limitation**: Changes API semantics, less idiomatic.

## Comparison with Other Languages

### Rust
```rust
fn try_lock() -> Option<MutexGuard<T>>  // Supported
```

### C++
```cpp
std::optional<std::lock_guard<T>>  // Supported (since C++17)
```

### Java
```java
Optional<Lock<T>>  // Supported
```

### Python (typing)
```python
def try_lock() -> Optional[MutexGuard[T]]:  // Supported
```

**All major statically-typed languages support nested generics.**

## Impact

### Blocked Features
- ❌ Non-blocking lock acquisition (`try_lock()`)
- ❌ Non-blocking read-write locks (`try_read()`, `try_write()`)
- ❌ Any API returning optional generic types
- ❌ Complex generic data structures (e.g., `Vec<Option<T>>`, `Result<Vec<T>, E>`)

### Workarounds Needed
- 324-line `sync.spl` module cannot be used as-is
- All stdlib APIs using nested generics need restructuring
- Ergonomics and type safety compromised

## Proposed Solutions

### Solution 1: Fix Parser (Recommended)

**Approach**: Implement proper nested generic parsing with lookahead or backtracking.

**Implementation Strategy**:
1. When parsing `<`, track nesting depth
2. Only close generic list when depth returns to 0
3. Handle `>>` ambiguity with context (type position vs expression)

**Estimated Effort**: Medium (1-2 days)
- Modify parser to track generic depth
- Add tests for nested generics (2, 3, 4+ levels)
- Handle edge cases (`>>`, `>>>`)

**Benefits**:
- ✅ Full language feature parity with modern languages
- ✅ No API compromises needed
- ✅ Future-proof for complex generic patterns

### Solution 2: Temporary Workaround

**Approach**: Comment out affected methods, document limitation.

**Implementation**:
```simple
# TODO: [parser][P1] Requires nested generic support (#XXXX)
# fn try_lock() -> Option<MutexGuard<T>>:
#     """Non-blocking lock acquisition."""
#     val value = rt_mutex_try_lock(self._handle)
#     if value == nil:
#         return nil
#     return Some(MutexGuard(self, value))
```

**Benefits**:
- ✅ Quick fix (30 minutes)
- ✅ Documents limitation clearly
- ✅ Allows rest of sync.spl to load

**Drawbacks**:
- ❌ Incomplete API surface
- ❌ Users can't use try_* methods
- ❌ Technical debt

## Recommended Action

1. **Immediate (today)**: Apply Workaround 2 to unblock sync.spl loading
2. **Short-term (this sprint)**: Implement Solution 1 (fix parser)
3. **Testing**: Add comprehensive nested generic tests
4. **Documentation**: Update language guide with nested generic examples

## Related Issues

- Generic syntax migration (`<>` vs `[]`) - recently completed ✅
- Type inference limitations - partially addressed
- Parser error messages - need improvement for generic errors

## Test Cases Needed

```simple
# 2-level nesting
fn test1() -> Option<Vec<i32>>
fn test2() -> Result<Map<String, i32>, Error>

# 3-level nesting
fn test3() -> Option<Result<Vec<String>, Error>>

# With type constraints
fn test4<T: Display>() -> Option<Box<T>>

# Edge case: >> ambiguity
fn test5() -> Vec<Vec<i32>>  # Should NOT parse as Vec<Vec<i32>>

# In struct fields
struct Container:
    data: Option<Vec<String>>

# In function parameters
fn process(items: Vec<Option<T>>) -> Vec<T>
```

---

**Status**: ✅ RESOLVED
**Priority**: P1 (High - blocks core stdlib) → Completed
**Complexity**: Medium
**Date**: 2026-01-12
**Resolved**: 2026-01-18
**Reported By**: Claude (Simple Language Compiler Team)

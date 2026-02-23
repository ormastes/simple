# Design Decision: No Exception Support in Simple Language

**Status**: Decided
**Date**: 2026-01-22
**Decision**: Simple language does not support exceptions (try-catch-throw)

## Decision

Simple language **will not implement exception handling** with try-catch-throw syntax. Instead, errors are handled through explicit return types using `Result<T, E>` and `Option<T>`.

## Rationale

### 1. Explicit Error Handling

**Exceptions are invisible control flow**:
```rust
// In languages with exceptions - unclear what can fail
val result = doSomething()  // Could throw anything!
```

**Result types make errors explicit**:
```simple
// In Simple - error handling is visible
val result: Result<User, Error> = findUser(id)
match result:
    case Ok(user): print user.name
    case Err(e): print "Error: {e}"
```

### 2. Performance and Predictability

- **No runtime overhead** of exception unwinding
- **No hidden control flow** - all error paths are explicit
- **Easier to reason about** - no unexpected throws deep in call stack
- **Better for embedded systems** - no exception tables needed

### 3. Aligned with Modern Language Design

Simple follows languages like:
- **Rust**: Uses `Result<T, E>` and `Option<T>`
- **Go**: Multiple return values `(value, error)`
- **Swift**: Optional types and Result
- **Zig**: Error unions

### 4. Simpler Compiler and Runtime

- No exception handling tables
- No stack unwinding mechanism
- No RTTI (Run-Time Type Information) for exception types
- Smaller binary size

## Error Handling Patterns

### Pattern 1: Result<T, E>

**For operations that can fail**:
```simple
fn divide(a: i32, b: i32) -> Result<i32, text>:
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

# Usage
match divide(10, 2):
    case Ok(result): print "Result: {result}"
    case Err(msg): print "Error: {msg}"
```

### Pattern 2: Option<T>

**For operations that may have no value**:
```simple
fn find_user(id: i32) -> Option<User>:
    if users.contains(id):
        return Some(users[id])
    return None

# Usage
match find_user(42):
    case Some(user): print user.name
    case None: print "User not found"
```

### Pattern 3: Try Operator (?)

**For propagating errors**:
```simple
fn process() -> Result<User, Error>:
    val data = read_file("users.json")?  # Propagates Err if read fails
    val user = parse_user(data)?          # Propagates Err if parse fails
    return Ok(user)
```

### Pattern 4: Panics for Unrecoverable Errors

**For programming errors (not user errors)**:
```simple
fn get_user(id: i32) -> User:
    if not users.contains(id):
        panic("BUG: user {id} must exist")  # Programming error
    return users[id]
```

## Migration from Exception-Based Code

### Before (Hypothetical Exceptions)
```simple
# NOT SUPPORTED
try:
    val result = risky_operation()
    process(result)
catch e:
    print "Error: {e}"
```

### After (Result-Based)
```simple
# SUPPORTED
match risky_operation():
    case Ok(result):
        process(result)
    case Err(e):
        print "Error: {e}"
```

## Promises and Async Errors

Promises use Result for error handling:

```simple
# Promise<Result<T, E>> pattern
fn async_operation() -> Promise<Result<User, Error>>:
    return Promise.new(\resolve, reject:
        match database.query():
            case Ok(user): resolve(Ok(user))
            case Err(e): resolve(Err(e))
    )

# Usage
val promise = async_operation()
match await promise:
    case Ok(user): print "Success: {user.name}"
    case Err(e): print "Failed: {e}"
```

## Comparison with Other Languages

| Language | Error Handling |
|----------|----------------|
| **Python** | Exceptions (try-except) |
| **Java** | Checked exceptions (try-catch) |
| **JavaScript** | Exceptions (try-catch) + Promises |
| **Rust** | Result<T, E> ✅ |
| **Go** | Multiple returns (value, error) ✅ |
| **Swift** | Optional + Result + try? |
| **Simple** | Result<T, E> + Option<T> + panic ✅ |

## Benefits of This Decision

1. **✅ Explicit**: All error paths visible in code
2. **✅ Performance**: No unwinding overhead
3. **✅ Predictable**: No hidden control flow
4. **✅ Composable**: Easy to chain with `?` operator
5. **✅ Type-safe**: Errors are typed and checked
6. **✅ Simpler runtime**: No exception machinery needed

## Trade-offs

### What We Lose
- ❌ Automatic stack unwinding
- ❌ Single error handling point for multiple calls
- ❌ Familiar syntax for Python/Java developers

### What We Gain
- ✅ Explicit error handling
- ✅ Better performance
- ✅ Simpler runtime
- ✅ Aligned with modern systems languages

## Implementation Status

- ✅ `Result<T, E>` enum implemented
- ✅ `Option<T>` enum implemented
- ✅ Pattern matching works
- ✅ Try operator (`?`) implemented
- ✅ Panic support exists
- ❌ No try-catch syntax (intentionally)
- ❌ No throw syntax (intentionally)

## Documentation Updates Needed

Files that need updating to remove exception references:
1. `src/lib/std/src/concurrency/promise.spl` - Remove try-catch blocks
2. `test/lib/std/unit/concurrency/promise_spec.spl` - Update test expectations
3. `doc/guide/deeplearning.md` - Update error handling examples
4. Any other files mentioning try-catch

## Related Design Decisions

- See `doc/design/result_type.md` (if exists)
- See `doc/design/error_handling.md` (if exists)
- See `doc/guide/error_handling.md` (to be created)

## References

- Rust Book: Error Handling - https://doc.rust-lang.org/book/ch09-00-error-handling.html
- Go Error Handling - https://go.dev/blog/error-handling-and-go
- Swift Error Handling - https://docs.swift.org/swift-book/LanguageGuide/ErrorHandling.html

## Conclusion

Simple language uses **explicit error handling with Result<T, E>** instead of exceptions. This makes errors visible, improves performance, and simplifies the runtime while following modern language design principles.

**Key Rule**: If an operation can fail, return `Result<T, E>`. Use pattern matching to handle both success and error cases.

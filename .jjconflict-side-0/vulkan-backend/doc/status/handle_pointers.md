# Feature #28: Handle Pointers

**Status**: Implemented
**Difficulty**: 4
**Importance**: 3

## Summary

Handle pointers (`+T`) use handle pools for efficient allocation and generational safety. Full language integration with `new +` syntax.

## Syntax

```simple
let handle = new + MyObject { value: 42 }

# Access through handle (automatically resolved)
main = handle  # Returns 42

# Arithmetic works through handles
let a = new + 10
let b = new + 5
main = a + b  # Returns 15

# Struct access
struct Point:
    x: i64
    y: i64

let p = new + Point { x: 7, y: 3 }
main = p.x + p.y  # Returns 10
```

## Features

- [x] `HandlePool<T>` in runtime (common crate)
- [x] `Handle<T>` type with generational indices
- [x] `alloc()` for allocation
- [x] `resolve()` for safe access
- [x] Generational safety (stale handles detected)
- [x] `+T` type syntax in parser
- [x] `new +` allocation syntax
- [x] Language-level integration
- [x] Automatic dereferencing for operations

## Tests

### Runtime Tests (src/common/tests/manual_unique.rs)
- `handle_pool_allocates_and_resolves` - Tests HandlePool allocation and resolution

### Interpreter Tests (src/driver/tests/interpreter_tests.rs)
- `interpreter_handle_pointer_basic` - Basic handle pointer creation and usage
- `interpreter_handle_pointer_arithmetic` - Arithmetic through handle pointers
- `interpreter_handle_pointer_with_struct` - Handle pointer to struct with field access

## Implementation

- **Parser**: `new +` expression in parser.rs:1790
- **AST**: `Expr::New { kind: PointerKind::Handle, expr }`
- **Interpreter**: `Value::Handle(ManualHandleValue)` in lib.rs
- **Runtime**: `HandlePool<T>`, `Handle<T>` in common/manual.rs

## Related

- #25 Unique Pointers (implemented)
- #26 Shared Pointers (implemented)
- #27 Weak Pointers (implemented)

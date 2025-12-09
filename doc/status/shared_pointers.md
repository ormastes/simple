# Feature #26: Shared Pointers

**Status**: Implemented
**Difficulty**: 4
**Importance**: 4

## Summary

Shared pointers (`*T`) provide reference-counted ownership for shared data. Full language integration with `new *` syntax.

## Syntax

```simple
let shared = new * MyObject { value: 42 }
let copy = shared  # Reference count increases
# When all references dropped, object is freed

# Arithmetic works through pointers
let a = new * 10
let b = new * 5
main = a + b  # Returns 15
```

## Features

- [x] `Shared<T>` type in runtime (common crate)
- [x] Reference counting implementation
- [x] `alloc_shared()` in ManualGc
- [x] `downgrade()` to weak pointer
- [x] `*T` type syntax in parser
- [x] `new *` allocation syntax
- [x] Language-level integration
- [x] Automatic dereferencing for operations

## Tests

### Runtime Tests (src/common/tests/manual_unique.rs)
- `shared_and_weak_round_trip` - Tests Shared creation, downgrade to Weak, and upgrade

### Interpreter Tests (src/driver/tests/interpreter_tests.rs)
- `interpreter_shared_pointer_basic` - Basic shared pointer creation and usage
- `interpreter_shared_pointer_arithmetic` - Arithmetic through shared pointers
- `interpreter_shared_pointer_multiple_refs` - Multiple references to same value
- `interpreter_shared_pointer_with_struct` - Shared pointer to struct with field access

## Implementation

- **Parser**: `new *` expression in parser.rs:1788
- **AST**: `Expr::New { kind: PointerKind::Shared, expr }`
- **Interpreter**: `Value::Shared(ManualSharedValue)` in lib.rs
- **Runtime**: `Shared<T>` in common/manual.rs

## Related

- #25 Unique Pointers (implemented)
- #27 Weak Pointers (implemented)
- #28 Handle Pointers (implemented)

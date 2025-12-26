# Feature #27: Weak Pointers

**Status**: Implemented
**Difficulty**: 3
**Importance**: 3

## Summary

Weak pointers (`-T`) provide non-owning references that don't prevent deallocation. Full language integration with `new -` syntax.

## Syntax

```simple
let shared = new * 42
let weak = new - shared  # Create weak reference from shared

# Weak pointers don't prevent deallocation
# Must upgrade to access (returns Option)
```

## Features

- [x] `WeakPtr<T>` type in runtime (common crate)
- [x] `downgrade()` from Shared to Weak
- [x] `upgrade()` returns Option
- [x] Automatic invalidation when Shared dropped
- [x] `-T` type syntax in parser
- [x] `new -` allocation syntax
- [x] Language-level integration

## Tests

### Runtime Tests (src/common/tests/manual_unique.rs)
- `shared_and_weak_round_trip` - Tests Shared->Weak downgrade and upgrade, including invalidation after drop

### Interpreter Tests (src/driver/tests/interpreter_tests.rs)
- `interpreter_weak_pointer_from_shared` - Creating weak pointer from shared

## Implementation

- **Parser**: `new -` expression in parser.rs:1789
- **AST**: `Expr::New { kind: PointerKind::Weak, expr }`
- **Interpreter**: `Value::Weak(ManualWeakValue)` in lib.rs
- **Runtime**: `WeakPtr<T>` in common/manual.rs

## Related

- #25 Unique Pointers (implemented)
- #26 Shared Pointers (implemented)
- #28 Handle Pointers (implemented)

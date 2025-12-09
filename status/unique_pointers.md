# Feature #25: Unique Pointers

**Status**: Implemented
**Difficulty**: 4
**Importance**: 4

## Summary

Unique pointers (`&T`) provide move-only ownership with deterministic drop, separate from GC-managed memory.

## Syntax

```simple
# Create a unique pointer
let ptr = new & 42

# Access value (implicit deref)
main = ptr  # Returns 42
```

## Features

- [x] `new &` allocation syntax
- [x] `Unique<T>` type in runtime (common crate)
- [x] Move-only semantics
- [x] Deterministic drop
- [x] `into_inner()` consumption
- [x] Lifecycle tracking via `ManualGc`
- [x] `is_valid()` check
- [x] Deref for value access

## Tests

### Runtime Tests (src/common/tests/manual_unique.rs)
- `manual_gc_tracks_unique_lifetimes`
- `into_inner_consumes_pointer_and_updates_tracking`
- `standalone_unique_allows_mutation_without_tracking`

### Language Tests (src/driver/tests/)
- `runner_supports_unique_new`

## Implementation

- **common/manual.rs**: `Unique<T>`, `ManualGc`
- **Interpreter**: Handles `Expr::New { kind: PointerKind::Unique, .. }`
- **Value**: `Value::Unique(UniqueValue)`

## Related

- #24 GC-Managed Memory (default)
- #26 Shared Pointers (*T)
- #27 Weak Pointers (-T)
- #28 Handle Pointers (+T)

## Future Work

- Full borrow checking enforcement
- Move semantics at type level

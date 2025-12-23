# AGENTS

This file documents guidance for AI agents working on the Simple compiler repository.

## Recent Completions (2025-12-23)

### Type System Enhancements (#1330-1339)

Implemented tagged unions (algebraic data types) and bitfields for the Simple language type system.

**Implementation:**
- `src/type/src/tagged_union.rs` - TaggedUnion and UnionVariant types
- `src/type/src/bitfield.rs` - Bitfield types with automatic layout
- Extended `Type` enum with `TaggedUnion(String)` and `Bitfield(String)` variants

**Key Features:**
- Tagged unions with discriminants for pattern matching
- Generic union support (e.g., `Option<T>`, `Result<T,E>`)
- Exhaustiveness checking for match expressions
- Bitfield types with automatic offset calculation
- Support for 8-128 bit backing types (u8, u16, u32, u64, u128)
- FFI-compatible layouts

**Tests:** 10 comprehensive unit tests (3 for unions, 7 for bitfields)

**Documentation:** See `TYPE_SYSTEM_ENHANCEMENT.md` for full details.

## Development Guidelines

When working on type system features:

1. **Add new type variants** in `src/type/src/lib.rs` Type enum
2. **Create separate modules** for complex types (see `tagged_union.rs`, `bitfield.rs`)
3. **Include comprehensive tests** - aim for 3-7 unit tests per module
4. **Update substitution logic** in `Type::apply_subst()` for new variants
5. **Update `contains_var()`** for new variants that may contain type variables
6. **Export public API** through module declarations and `pub use`

## Testing Strategy

- Unit tests go in the same file (in `#[cfg(test)] mod tests`)
- Integration tests in `tests/` directory
- Run type tests: `cargo test -p simple-type`
- Run all tests: `make test`


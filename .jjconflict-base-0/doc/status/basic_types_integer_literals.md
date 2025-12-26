# Feature #1: Basic Types

**Status**: Interpreter Complete | Native Codegen: Stub
**Difficulty**: 1/5
**Importance**: 5/5

## Summary

Basic types (i8-i64, u8-u64, f32-f64, bool, str, nil) are fully supported in the tree-walking interpreter.

## Supported Types

| Type | Interpreter | Native Codegen |
|------|-------------|----------------|
| `i8`, `i16`, `i32`, `i64` | Working | Stub |
| `u8`, `u16`, `u32`, `u64` | Working | Stub |
| `f32`, `f64` | Working | Stub |
| `bool` | Working | Stub |
| `str` | Working | Stub |
| `nil` | Working | Stub |

## Implementation

### Interpreter (`src/compiler/src/interpreter.rs`)

The `Value` enum in `value.rs` represents all runtime values:

```rust
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(String),
    Nil,
    // ... other variants
}
```

Integer literals in `main = 42` are evaluated by the interpreter, then the result is packaged into an SMF binary.

### Native Pipeline (TODO)

For true native compilation:
1. HIR needs to lower integer literals to typed constants
2. MIR needs to represent typed integer values
3. Cranelift needs to emit `iconst` instructions

Current SMF generation just does:
```rust
// mov eax, <interpreter_result>; ret
code.push(0xB8u8);
code.extend_from_slice(&return_value.to_le_bytes());
code.push(0xC3);
```

## Tests

```bash
# Interpreter tests for basic types
cargo test -p simple-driver interpreter_integer
cargo test -p simple-driver interpreter_float
cargo test -p simple-driver interpreter_bool
cargo test -p simple-driver interpreter_string
```

## Next Steps

1. Implement HIR lowering for integer literals
2. Add MIR representation for typed constants
3. Wire Cranelift `iconst` generation

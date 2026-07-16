# Native mixed numeric ordering depends on operand order

- status: source fixed for signed integers 2026-07-16; dual-backend execution pending
- severity: high (possible silent wrong comparison)
- component: MIR numeric coercion, LLVM and Cranelift lowering

## Symptom

LLVM and Cranelift select integer versus float comparison from the left
operand. An integer-left/float-right comparison may therefore truncate or use
the wrong predicate, while reversing the operands follows the float path.

## Resolution

MIR now widens mixed signed-integer `<`, `<=`, `>`, and `>=` operands to f64
before either backend. Mixed numeric `==` and `!=` emit their type-strict
constant result only after both operands have been evaluated. The strict-dual
harness covers both operand orders, equal boundaries, signed zero, NaN, and
strict equality. Executable evidence awaits a runnable pure-Simple CLI.

Unsigned integer/float ordering requires unsigned-aware casts and remains in
`native_unsigned_float_ordering_codegen_2026-07-16.md`.

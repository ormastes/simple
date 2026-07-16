# Native mixed numeric ordering depends on operand order

- status: open
- severity: high (possible silent wrong comparison)
- component: MIR numeric coercion, LLVM and Cranelift lowering

## Symptom

LLVM and Cranelift select integer versus float comparison from the left
operand. An integer-left/float-right comparison may therefore truncate or use
the wrong predicate, while reversing the operands follows the float path.

## Required fix

MIR must widen mixed `<`, `<=`, `>`, and `>=` operands to a shared float type
before either backend. Keep mixed-kind `==` and `!=` type-strict. Verify both
operand orders, equal boundaries, signed zero, and NaN behavior on both
backends.

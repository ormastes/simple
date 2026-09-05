# Layer Expert: Interpreter Value Semantics

## Boundary rule

The AST/tree interpreter owns `Value`-level execution. A typed unsigned literal
that renders correctly but compares incorrectly has already crossed the parser
and literal-construction boundary intact; repair the `Value` operator owner,
not pure-Simple HIR/MIR lowering or the native runtime.

For integer ordering, use the shared unsigned-aware helper in
`src/compiler_rust/compiler/src/interpreter/expr/ops.rs`. `Value::as_int()` is
appropriate for bit-pattern operations but is not an ordering conversion for
`Value::UInt`. Keep relation operators symmetric and cover mixed signed values.

## Review checks

- Verify direct literals and struct fields preserve unsigned rendering.
- Exercise the failing value through its full container/Option boundary, not
  only through the comparison helper.
- Cover the sign edge and maximum: `2^63 - 1`, `2^63`, `2^63 + 1`, `u64::MAX`.
- A Rust-seed run is diagnostic evidence for this Rust-owned interpreter only;
  it is not a production pure-Simple or Stage 4 admission claim.

# Feature Expert: Interpreter Unsigned Semantics

## Authority

Simple integer suffixes define semantic width and signedness. The Rust
tree-interpreter represents unsigned integers as `Value::UInt { value, width }`;
it must not route ordering through `Value::as_int()`, because that API exposes
the same bits as `i64` and makes every high-bit `u64` appear negative.

The canonical relational owner is `integer_ordering` in
`src/compiler_rust/compiler/src/interpreter/expr/ops.rs`. All four relational
operators share it. Mixed ordering follows mathematical integer order: a
negative `i64` is below every `u64`, while a high-bit `u64` is above every
non-negative `i64` it exceeds.

## Regression evidence

- Exact language boundary:
  `test/01_unit/compiler/interpreter/u64_high_bit_option_unwrap_spec.spl`
- Owner-level exact and adjacent boundaries: the `integer_ordering_*` Rust
  tests cover `2^63 - 1`, `2^63`, `2^63 + 1`, `u64::MAX`, and mixed signs.
- Tracked incident:
  `doc/08_tracking/bug/interp_u64_high_bit_option_unwrap_corruption_2026-07-11.md`

Do not mask hashes to 63 bits as a semantic fix. A producer workaround may
remain for compatibility, but interpreter ordering must preserve all 64 bits.

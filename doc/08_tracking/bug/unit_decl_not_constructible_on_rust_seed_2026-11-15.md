# `unit Name: T` is not a constructible type on the Rust seed

Date: 2026-11-15
Status: partly fixed (construction + suffix-less form); operators on one-field records still open

## Fixed (seed, this change)
1. `unit ByteCount: u64 as Bc` then `ByteCount(value: 7)` failed with
   `semantic: function 'ByteCount' not found`. A single-base standalone `unit` now also
   registers a constructible one-field `value` class (same shape as numeric `newtype`),
   at module level (`interpreter_eval.rs`) and block level (`interpreter/node_exec.rs`),
   via `unit_constructor_class` in `interpreter_unit.rs`. Literal-suffix behaviour
   (`42_uid`) is unchanged. Multi-base `unit IpAddr: str | u32 as ip` stays literal-only.
2. `unit BitCount: u64` (no `as suffix`) was a parse error (`expected As`). The suffix is
   now optional (`UnitDef.suffix == ""`, no suffix registered).
Tests: `parser/tests/type_tests.rs` (`test_unit_without_suffix*`),
`driver/tests/interpreter_unit_types.rs` (`interpreter_unit_decl_*`),
`test/01_unit/compiler/frontend/unit_decl_e2e_spec.spl` (3/3 on the built seed:
construct + `.value`, pass to function, struct field).

## Remaining (not parser; out of this PR)
Operators on any one-field record fail on the seed, `newtype` included:
`newtype B = i64; val a = B(value: 10); (a + a)` => `semantic: type mismatch: cannot
convert object to int` (also `<`, `*`, `3 * a`; `==` works). JIT first demotes with
`HIR lowering error: ... cannot infer field type ... struct 'ANY' field 'value'`.
The interpreter has newtype-wrap code in `interpreter/expr/ops.rs` (~693) but the
failure happens before it is reached (reported as `compile failed`). The removed spec
examples (same-unit +/-, scale by int, compare, `b * 2`, `buf.size + by`) must return
once this is fixed.

Still blocked: migrating `nvme_ct.spl` to `unit` needs a deployed seed containing this
change, and operator use on units needs the operator fix above.

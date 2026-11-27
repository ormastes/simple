# `unit Name: T` is not a constructible type on the Rust seed

Date: 2026-11-15
Status: fixed on the seed (construction, suffix-less form, same-unit operators)

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
8/8 on the built seed incl. operators).

3. Operators on one-field records failed on the seed (`newtype` included): `(a + a)` =>
   `semantic: type mismatch: cannot convert object to int`. Cause: class instances are
   `Value::ClassInstance`, but the newtype-wrap code in `interpreter/expr/ops.rs` and
   `Value::as_int` only knew `Value::Object`. Both now accept a method-less class
   instance whose only field is `value`. Result types: U+U, U-U, U%U, U*n, n*U, U/n give U;
   U*U and U/U give the bare scalar; comparisons work. No cross-unit deny check on the
   seed (the pure-Simple compiler enforces that).

## Remaining
Migrating `nvme_ct.spl` to `unit` needs a deployed seed containing this change.

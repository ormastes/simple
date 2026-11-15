# Unit construction from a primitive is unsupported at runtime (blocks stdlib boundary migration)

Found by lane stdlibmig, 2026-11-15, with `bin/simple.exe run` on a file declaring
`unit FreeBytes: i64 as fbytes`:

- `FreeBytes(5)` -> `error[E1002]: function FreeBytes not found`
- `5 as FreeBytes` -> `semantic: type mismatch: cannot cast i64 to FreeBytes`
- only the literal suffix `5_fbytes` constructs a value; `.value` also fails JIT type inference.

SPL-BOUND-001/002 tell authors to build the unit inside an
`@unsafe(capabilities: [ffi])` adapter (`Unit(raw)` / `raw as Unit`), which is
therefore not executable today. Migrating a stdlib boundary (slice H) would break
runtime callers. Needs: a working primitive-to-unit constructor in the runtime
path (repro: the 4-line file above). Repro/prevention spec to be added with the fix.
Status: verification-pending (fix landed on work/rb3-unitctor-20261115; not yet natively verified). Baseline: doc/08_tracking/test/robust_boundary_stdlib_census_2026-11-15.md

## Fix (lane rb3-unitctor, 2026-11-15)

- Seed (`src/compiler_rust`): `Name(raw)` (`interpreter_call/mod.rs`, before the
  record-class fallback) and `raw as Name` (`interpreter/expr/casting.rs`) build
  the same `Value::Unit` as the `raw_sfx` literal, via
  `interpreter_unit::{standalone_unit_suffix, construct_standalone_unit}`.
  `u.value` field access now works on a unit value (`interpreter/expr/calls.rs`).
  Non-unit names still error ("cannot cast i64 to X"), and so do non-numeric raw
  values. Rust unit tests are in `interpreter_unit.rs` (`standalone_unit_ctor_tests`).
- Pure Simple (`src/compiler/20.hir`): a unit already lowers to the one-field
  record `Name { value: T }`, so `Name(raw)` is the record constructor.
  `raw as Name` now lowers to that record's `StructLit` in the HIR Cast arm.
- Spec: `test/01_unit/compiler/unit_from_primitive_construction_spec.spl`.
- Gap: the pure-Simple lane has not been run (no deployed full-CLI pure-Simple
  binary). On that lane, the methods `.value()` / `.to_f64()` exist only for the
  seed's `Value::Unit`; the pure record exposes the `.value` field.

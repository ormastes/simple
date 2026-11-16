# Seed HIR: `.value` field on an imported `unit` newtype fails to lower

- **Status:** verification-pending
- **Component:** Rust seed HIR lowering (`src/compiler_rust/compiler/src/hir/lower/import_loader.rs`)
- **Found:** 2026-11-17, native-build of `src/lib/nogc_sync_mut/io/native_tool_authority_v1.spl:227`
  (as of 077536f9f13; now worked around with plain structs there and in `disk_admission.spl`)

## Symptom
`hir: Unsupported feature: cannot infer field type while lowering <fn>: struct 'ANY' field 'value'`
for `pin.digest.value` (`pub unit Sha256Hex: text`, `Pin.digest: Sha256Hex`) and for
`f.value` bound by `case Some(f)` over `FreeBytes?` (`pub unit FreeBytes: i64 as fbytes`).

## Root cause
Within one module, `register_record_unit_scalar` (module pass) aliases a scalar
record unit to its base type, and field access treats `.value` on that scalar as
the identity. The import loader never registered `Node::Unit` items, so in the
IMPORTING module the unit name did not resolve: imported struct fields, fn
return types and params using it became ANY, and `.value` then hit the
dynamic-field diagnostic. Single-module fixtures do not reproduce; repro needs
an import (confirmed with seed `native-build` on a two-file fixture).

## Fix
`import_loader.rs`: before full registration of an imported module's items,
call `register_record_unit_scalar` for every `Node::Unit` in it (all items, as
struct fields may reference non-imported units of the same file).

## Tests
`src/compiler_rust/compiler/src/hir/lower/tests/unit_value_field_tests.rs`:
- `imported_unit_value_field_through_loop_var_lowers` (red before fix)
- `imported_unit_value_field_on_option_pattern_binding_lowers` (red before fix)
- `dynamic_value_field_with_ambiguous_owners_still_fails_closed` (guard)

## Verification pending
Native verification: seed native-build with the `unit` forms restored in
`native_tool_authority_v1.spl` / `disk_admission.spl` (workarounds can then be removed).

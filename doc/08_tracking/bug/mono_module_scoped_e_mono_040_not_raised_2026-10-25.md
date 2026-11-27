# Module-scoped mono: E-MONO-040 not raised for imported generics (2026-10-25)

Status: FIXED (branch work/mono-generic-marker)

## Symptom
`test/01_unit/compiler/mono/mono_module_scoped_spec.spl` case "fails closed with
E-MONO-040 when the template is not visible" failed (3/4): with no visible
templates, a call to an imported generic (`use t.{id}`; `id(1)`) produced no
diagnostic, so the per-file lane could emit objects with unresolved generic calls.

## Root cause
HIR import registration stores no signature type for generic callables
(`declared_imported_surface_callable_type` returns nil when `type_params` is
non-empty). `module_scoped_visibility_check_v1` only counted a non-nil,
non-concrete `type_` as generic evidence, so a nil type read as "not generic".

## Fix
- `HirSymbol.generic_param_count: i64 = 0` — explicit generic marker.
- Import registration sets it from `ModuleSurfaceCallable.type_params.len()`
  (`SymbolTable.mark_generic_callable`); `rename_symbol` preserves it.
- Mono reads the marker first. A missing type is still NOT treated as generic.

## Known limit
The generated HIR codec (`20.hir/generated/hir_codec.spl`) does not serialize the
field; cache-decoded symbols default to 0. Regenerate the codec to carry it.

## Evidence
mono_module_scoped_spec 4/4 (was 3/4). generic_template_spec 20/20.
instantiation_missing_template_spec 0/1 and generic_fn_specialization_breadth_spec
5/6 fail identically on the unpatched base (pre-existing).

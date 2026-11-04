# HIR import specs drifted from owner/surface API (2026-11-04)

Status: partially fixed (spec-only; product unchanged).

- resolve_import_module_value_spec.spl: built `ModuleSurfaceParserOwner(parsed_path: ...)`
  by hand; the class has no `parsed_path` field and many required fields. Now uses
  `ModuleSurfaceParserOwner.new(provider)`. 0/2 -> 2/2.
- resolve_import_symbols_spec.spl: called `module_surfaces_from_test_modules`
  without importing `test.helpers.module_surface_owner_fixture`, `ModuleSurfacesByName`,
  `Module`, `SourceFile`. Imports added. 1/38 -> 24/38.

Still open (not fixed here):
- resolve_import_symbols_spec: 14 remaining failures (missing-item diagnostics not
  emitted, `owner_module` nil) - likely product regression.
- reexport_cycle_memo_spec: uses removed `find_reexport_source(facade, mod, name, 0)`
  signature and removed `reexport_count()`; needs redesign against index-based API.
- imported_positional_struct_owner_spec: `HirLowering.positional_struct_pattern_field_order` removed.
- field_index_erased_receiver / field_index_guess_class: fixture BUILD-FAILED.

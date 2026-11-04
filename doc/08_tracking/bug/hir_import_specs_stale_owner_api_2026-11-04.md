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

## resolve_import_symbols_spec: 24/38 -> 34/38 (2026-11-04, follow-up)

Root causes of the 14 (not one defect):
- Product regression (fixed, 4 examples + 1 control): commit 438d2c63f07 (2026-08-22)
  made `module_surface_explicit_import_origin` read `import_target_indices`, which
  `module_surfaces_freeze` only publishes AFTER `resolve_export_origins` runs
  (`module_surfaces_from_modules`: resolve -> finish). So no explicit-import facade
  export origin was ever recorded (`export_origins[..]` nil -> `owner_module` nil).
  Fix: derive the owner from the import declaration via `name_index` while the scalar
  route is not yet published (`module_surface_export_index.spl`).
- Product gap (fixed): `export use M.{a}` is recorded qualified (`M.a`, 1670c0f64ea,
  parser) with no matching ImportItem, so no origin was derived. Added
  `module_surface_qualified_export_origin` (first pass + fixpoint revisit).
- Intentional redesign (spec updated): e05dbf566db (2026-10-20, seed parity) downgrades
  "module X has no exported item Y" to the `[hir-reexport-chase-unresolved]` receipt;
  the two missing-item examples now assert 0 import-site errors + the local name stays bound.
- Stale spec API (spec updated): 3 examples assigned the removed
  `HirLowering.modules_by_name` (now `hirlowering_for_module(name, surfaces)`);
  `SymbolTable.get` -> `get_symbol`.

Still failing (4, not fixed, separate causes):
- "unbraced renamed re-export": parser records the export item as
  `alias.provider.orig.alias.provider.orig:public_orig` (path doubled) for
  `export use alias.provider.orig as public_orig` -> parser defect.
- "keeps a complete module alias" and "binds a relative mod namespace": likely the gap where
  the pre-freeze name_index fallback does not handle relative-dot paths or the
  `use a.b.item as x` parent-fallback that freeze's resolution trace handles
  (registry_index.spl ~570-610).
- "module-qualified imported function call" (`fn_.body.stmts` empty): uninvestigated.

Regression comparison (original vs fixed export_index.spl, 14 neighbouring import/reexport/surface
specs that fail after the fix): identical counts in 13; same_named_package_facade_reexport 0/5 -> 2/5;
module_surface_semantic_projection hangs/times out both before and after. 19 other neighbouring
specs pass after the fix. No pass->fail.

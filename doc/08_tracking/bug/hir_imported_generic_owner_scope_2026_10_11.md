# Imported generic composite field owner scope

Status: OPEN; draft repair and regression fixture AUTHORED_UNEXECUTED.

Observed Phase 4 Caret suite producer 4cca9585 emits unresolved Op/Cpl diagnostics for imported SimpleRing<Op,Cpl>. Source inspection confirms ModuleSurfaceComposite retains parameters, but imported field dependency registration and projection did not bind them. Local prescan_composite_field_types already provides a saved/restored binder scope.

Draft repair filters declared owner parameters from transitive dependency materialization, installs a lexical Class scope for field projection, preserves TypeParam names/bounds through the existing prescan parameter map, and restores consumer state. Both scalar and nested imported projections prefer active owner binders over qualified same-spelled module declarations. Non-generic dependencies remain materialized in the existing consumer scope.

Regression: test/fixtures/native/imported_generic_owner_scope/{owner,main}.spl covers imported generic class/struct fields, optional and array containers, nested generic Packet<Op>, and same-spelled owner/consumer decoys. Existing imported_generic_fields is the non-generic dependency control. Main returning zero is not semantic execution evidence. Admission requires actual HIR field-map checks, concrete specialization and executed field reads, plus normal compiler/core/MCP verification. No producer rebuild or PASS claimed yet.

Related but distinct: explicit call type arguments are discarded in the parser; inferred optional generic results can produce Some(nil). This field-scope draft does not claim to fix those call-transport defects.

Astra source review accepted saved/restored owner scope, dependency filtering and binder-first projection; review identified optional has_X sugar and exact has_-prefixed binder preservation, now included. Review does not establish executable qualification.

**Revalidated 2026-11-02: still plausible because OPEN; draft repair and regression fixture AUTHORED_UNEXECUTED; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 lane s3g3: fix-implemented-verification-pending
- The draft repair is already in the tree: commit `e14301086a9` (2026-10-10) added owner-parameter-filtered
  `materialize_imported_composite_field_dependency`, the lexical `ScopeKind.Class` scope plus
  `project_imported_owner_type_parameters` and saved/restored `prescan_type_parameters` in
  `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl` (~lines 667-722); regression
  fixture `test/fixtures/native/imported_generic_owner_scope/{owner,main,construction}.spl` (`ba43b600708`).
- Remaining: executed evidence only. Verify with a stage3 `check`/`native-build` of `main.spl` (no
  unresolved `Op`/`Cpl`), then `construction.spl` must exit 0 with empty stdout/stderr.

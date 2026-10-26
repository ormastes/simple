# `...entity_view.TypedAstView.{X}` import fails; entity_view __init__ re-exports are empty

- Date: 2026-10-26 | Owner area: module resolver + src/compiler/85.mdsoc/transform/feature/*/entity_view | Size: M
- Symptom: test/01_unit/compiler/mdsoc/transform_adapters_spec.spl ERROR before any example:
  `Module "compiler.mdsoc.transform.feature.typing_to_hir.entity_view" does not export 'TypedAstView'`.
- Evidence: spec lines 16-23 import `entity_view.TypedAstView.{TypedAstContext}` etc. Files exist
  (typing_to_hir/entity_view/TypedAstView.spl) but the resolver treats the PascalCase last segment as an item of the
  directory module `entity_view` (snake_case file imports like feature/desugaring/app/desugar_input_port work).
  Workaround tried and reverted: importing `entity_view.{TypedAstContext}` loads, but every example then fails with
  `semantic: unknown class TypedAstContext` because entity_view/__init__.spl is only `export TypedAstContext`
  (bare export, no `use`), i.e. it re-exports nothing. Same shape in all 8 entity_view dirs.
- Fix (either): rename files to snake_case (typed_ast_view.spl ...) and update imports/`expose` in each
  transform/feature/*/__init__.spl:21-32; or make the resolver prefer a file over an item when both fit; and make
  entity_view/__init__.spl real re-exports (`export use ...TypedAstView.{TypedAstContext}`).
- Repro: `bin/simple.exe test test/01_unit/compiler/mdsoc/transform_adapters_spec.spl --no-session-daemon`

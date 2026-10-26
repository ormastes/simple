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

## Resolution (2026-10-27) - FIXED, spec 67/67
- Root cause (two layers): (1) the module resolver only resolves a file import up to 6 path segments
  (`compiler.mdsoc.transform.feature.<pair>.entity_view.<file>` is 8, so `<file>` was treated as an item of the
  directory module; probed: `...feature.ev3.hir_view` (6) resolves, `...feature.hir_to_mir.ev4.hir_view` (7) does not,
  independent of PascalCase vs snake_case); (2) each `entity_view/__init__.spl` was a bare `export X` that re-exports nothing.
- Fix: `entity_view/__init__.spl` (all 8 transform pairs) now re-exports with a relative `export use .<file>.{Type}`
  (mir_to_backend: MirDebugInfo, MirProgram); the 11 PascalCase files were `git mv`'d to snake_case
  (typed_ast_view.spl, hir_view.spl, ...) for consistency with sibling packages and the `exports { expose = [...] }`
  entries in each `transform/feature/*/__init__.spl` updated; transform_adapters_spec.spl now imports
  `...<pair>.entity_view.{Type}` (7-segment package path).
- Verdict before: ERROR executed=0. After: OK executed=67 passed=67 failed=0.
- Remaining: the resolver's 6-segment file-import limit is a seed/resolver bug, not fixed here.

# HIR: imported callable signature has no package-sibling fallback (2026-08-22)

**Status: RESOLVED** (same day). Class 2 of the stage1-closure HIR fatals.

## Symptom
Stage1 closure probe (no `SIMPLE_BOOTSTRAP`):
`[hir-fatal] src/compiler/blocks/sugar_registry.spl: unresolved type: Completion`
(also blamed on `15.blocks/blocks/{context,modes,value}.spl`; earlier runs
named `HighlightToken` / `BlockExample` from the same owner). The blamed
modules never mention `Completion`; sugar_registry.spl has no `use` line at all.

Reproduced without the closure: `bin/simple native-build
src/compiler/15.blocks/blocks/builtin_blocks_data.spl --threads 8` (11-module
graph) -> 56 `[hir-fatal]` lines, all `unresolved type: {Completion,
HighlightToken, BlockExample}` on context.spl / modes.spl / value.spl.

## Root cause
`resolve_package_sibling_symbols` registers every package member's public
symbols into a zero-import member. Registering `SqlBlockDef` from
`builtin_blocks_data.spl` eagerly lowers its impl method signatures
(`fn completions(...) -> [Completion]`). `Completion` is declared in the
directory sibling `definition.spl` and reached only by directory-sibling
visibility (no `use`). `materialize_imported_callable_type_dependencies_inner`
tried only (1) the owner's own declarations and (2) its explicit `use` items;
the composite-FIELD twin (`materialize_imported_field_dependency_inner`) had
grown a third step, the unique package sibling
(`materialize_imported_field_package_dependency`), but the callable twin never
did. Whenever the registry lists the impl owner BEFORE the type owner
(`builtin_blocks_data` < `definition`), the signature lowers before
`Completion` is bound and `lower_named_kind` hard-errors, blamed on whichever
member is being lowered.

## Fix
`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`:
the six duplicated declared->explicit blocks become one
`materialize_imported_callable_dependency` that adds the package-sibling step,
mirroring the field twin exactly (unique declaring sibling only; ambiguous
short names are left alone).

## Regression spec
`test/01_unit/compiler/hir/package_export_route_shapes_spec.spl` (mirrored),
`sibling impl method whose return type is a directory-sibling type` and
`tier-aliased package: ...` (registry order impl-owner-first). 3 examples fail
pre-fix with the exact text, 26/26 post-fix. Real rebuild of the 11-module
graph above: 56 -> 0 `[hir-fatal]`.

## Exposed next (NOT fixed here, different layer)
With HIR clean, the same build now stops in MIR:
`MIR lowering error: undefined variable CompletionKind` —
`builtin_blocks_data.spl` uses `CompletionKind.Keyword` through
directory-sibling visibility and MIR has no sibling enum binding for it.

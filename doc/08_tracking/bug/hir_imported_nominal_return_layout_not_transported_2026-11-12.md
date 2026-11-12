# HIR does not transport the layout of an imported callable's third-module return type

- **Status:** open
- **Severity:** P2 (lint false positive plus missing layout for downstream consumers)
- **Found:** 2026-11-12, audit-fixes lane
- **Spec:** `test/01_unit/compiler/lint/frontend_diag/inferred_type_fallback_use_spec.spl`
  (3 red examples: "retains the exact third-module return layout without a direct
  type import", "retains the exact return layout when only the facade function is
  imported", "does not fire when the type arrives through a re-exporting facade
  imported with a glob")

## Reproduction

`lib.model` declares `struct Node(n: i64)`. `lib.api` imports it and declares
`pub fn node_get(i: i64) -> Node`. The consumer imports only `lib.api.{node_get}`
(or `lib.api.*`, where `lib.api` has `export use lib.model.*`). It then lowers
`val src = node_get(0); src.n`.

Observed on the phase-1 seed (probe, 2026-11-12):

- `node_get` symbol type is `Function([i64], Named(SymbolId 0))`, so the signature IS transported.
- `Node` is registered as SymbolId 0 (qualified bind through
  `materialize_imported_callable_declared_dependency_inner`).
- `hir.structs.len() == 0`. No layout exists for SymbolId 0.

## Root cause

`HirModule.structs` (built in `20.hir/hir_lowering/_Items/module_build.spl`
around lines 456 and 766) contains only the lowered module's OWN `module.structs`.
Imported-callable dependency materialization
(`_Items/module_reexport_materialization.spl`) registers and binds the
symbol, but no channel carries the defining module's field layout into the
importer's HIR. The lint `hir_frontend_type_unresolved`
(`35.semantics/lint/hir_frontend_diagnostics.spl:161`) first checks
`hir.structs/classes/enums.contains_key(sym)`. That misses. It falls back to
import-list heuristics: the consumer imports neither `lib.model` nor the name
`Node`. So it reports W-HIR-INFER-001.

## Why this was not fixed in place

Inserting imported layouts into `HirModule.structs` would make the importer
appear to OWN them. MIR consumers treat `hir_module.structs` as the module's
own declarations: `50.mir/hir_declaration_summary_v1.spl`,
`_MirLowering/declaration_providers_v1.spl`, `provider_metadata.spl`,
`bootstrap_globals.spl` cfg winners, and `bootstrap_type_registration.spl`.
Doing that risks duplicate declarations or providers across modules. The
correct fix is a separate, non-owning carrier, for example
`HirModule.imported_layouts: Dict<SymbolId, HirStruct>`. Materialization
would fill it from the declaring surface. The lint would consult it, and the
spec probe `imported_node_return_has_layout` would read it, not `structs`.
That is a HIR data-model change across 20.hir/35.semantics/50.mir and needs
an owner design decision.

## Related

- `hir_any_alias_and_inferred_fallback_diag_gaps_2026-10-30.md` ("nominal owner
  transport remains OPEN"; these positives were authored NOT_RUN)
- `stage2_imported_fn_foreign_struct_return_type_erased_2026-10-10.md`

## Spec correction landed with this record

"does not classify a deliberately deferred generic imported signature" expected
`symbol.type_.?` to be false. The current surface transports the polymorphic
signature `fn(T) -> T`, and no warning fires. The expectation now asserts that
the result stays `TypeParam(T)`, which is the real "deferred" invariant.

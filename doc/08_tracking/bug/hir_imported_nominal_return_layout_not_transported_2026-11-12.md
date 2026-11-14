# HIR does not transport the layout of an imported callable's third-module return type

- **Status:** verification-pending
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

## Fix (2026-11-12, work/hir-imported-layouts-20261112)

Implemented the recommended non-owning carrier:
`HirModule.imported_layouts: Dict<SymbolId, HirStruct> = {}` (`20.hir/hir_types.spl`).
`register_imported_symbol`'s composite branch
(`_Items/module_import_registration.spl`) fills it for every imported
struct. It uses the importer-projected surface field types that are already
computed for `struct_field_types_by_name`. `HirModule.structs` is unchanged,
so the MIR declaration and provider consumers see no new owner. The lint
`hir_frontend_type_unresolved` also consults `imported_layouts`. The spec probe
reads `imported_layouts` and asserts that `structs` does NOT own the symbol.
Result: `inferred_type_fallback_use_spec` went from 22/25 to 25/25 on the phase-1 seed.
Native verification is still pending.

## Narrowed 2026-11-14: the side table carries identity, not a field copy

The fix above stored a full `HirStruct` (one `HirField` per declared field)
for every imported struct in every importer. On the run-32 full CLI closure
(3145 modules) those copies were 30 % of all encoded HIR fields (165 rows,
1200 fields per module; 31-entry sample of the HIR cache) and nothing after
lowering reads them: the lint asks `imported_layouts.contains_key(sym)`, and
no consumer in 50.mir / 60 / 70 / 80 names the field.

`hir_imported_struct_row_v1` (`20.hir/hir_lowering/imported_layout_row_v1.spl`)
now builds an identity-only row (importer SymbolId, declaring name, visibility,
span, generic flag, `fields: []`). The key set is unchanged, so the lint result
is unchanged: `inferred_type_fallback_use_spec` stays 25/25 on the seed, with
its two layout-payload examples reworded to assert the nominal row (the
unedited file is 23/25 against this change, failing exactly those two).
New spec: `test/01_unit/compiler/20.hir/hir_imported_layout_row_spec.spl`
(8/8; red run 4/7 before the change, one control example added afterwards).

"Missing layout for downstream consumers" is therefore NOT delivered by this
table. A consumer that needs an imported struct's fields reads the declaring
module (`HirModule.structs` of the owner, as MIR does through `providers`).
Design and numbers: `doc/05_design/compiler/perf/hir_import_replica_residency_v1.md`.
Native verification (RSS, lint on a cache hit) is still pending.

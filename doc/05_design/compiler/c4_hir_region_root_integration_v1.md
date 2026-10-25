# HIR region root construction integration

Status: implementation plan, not a completed root-construction implementation. Actual parser/HIR acceptance remains UNRUN; full SOURCE remains open.

Required ABI: [dictionary region interface](c4_dictionary_region_interface_v1.md).

Owner: HIR authority integration lane. The earlier constructor/query candidate is uncommitted work, not a landed authority implementation; preserve and reconcile its changes against current HIR owners rather than replacing entire files.

The earlier constructor/query candidate in hir_lowering/types.spl executes SymbolTable.new(), then hir_admission_attach_v1(owner). That order cannot certify region ownership: all dictionaries and the root Scope already exist. The SOURCE request must select and specialize an actual constructor before the first dictionary/Scope birth, supplying the same runtime region context through the verified closed call graph. Ordinary construction remains ordinary.

Planned narrow integration points:

- hir_lowering/types.spl: SOURCE branch invokes the actual resolved specialized constructor; no post-birth adoption or caller boolean admission.
- hir_types.spl SymbolTable.new construction: dictionary literal and Scope construction sites pass through owner-phase typed dictionary/aggregate emission. Preserve root_scope_symbols identity shared with Scope.symbols, next IDs, indices and ordinary alias behavior.
- hir_source_admission_v1.spl bind_routing: consume actual region birth/publication facts, retain expected region epoch; dictionary identity/epoch guards remain additional checks, never substitutes for descendant closure.
- hir_source_scope_read_v1.spl and hir_source_driver_query_v1.spl: obtain prepaid short read lease, validate region stamp before projections, then preserve existing bounded dictionary read capability. Never refresh the view stamp because a raw alias wrote.
- hir_symbol_table_methods.spl and existing constructor write hooks: actual same-account authorized mutation permits prepay before stores and refresh only the publishing owner's stamp. Foreign attachment, capacity failure and generation mismatch cannot publish.

Prerequisites are production dependencies, not acceptable permanent restrictions: dictionary operations13–16 with actual raw-key read, typed before-boxing captures, struct mutation barriers, optional parent/ScopeKind enum codecs, text-key binding dictionaries and certified immutable text inputs, arrays/rich symbol types, verified runtime retained request/caller and final artifact authority. No source root can be marked complete while one reachable edge lacks owner support.

First native acceptance uses the real parser/HIR constructor and NoManifest query. Existing nested symbol.name, symbol.type_ and scope.parent aliases must produce Stale, including aliases acquired before first query. Add same-value updates, rehash/replacement then legitimate publication, foreign child refusal and fuel-one-short unchanged stores. Source-only fixture construction or a phase-final graph walk is insufficient. Tests remain UNRUN until root coordinates a qualified compiler; no exhausted primitive cycle is repeated.

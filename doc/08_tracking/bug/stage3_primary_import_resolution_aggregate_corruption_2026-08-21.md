# Stage-3 primary import resolution aggregate corruption (2026-08-21)

## Status

Claimed by the `codex/must-check-slang` lane for a fresh bounded repair
session. The prior session's third bootstrap cycle failed in Stage-3 HIR and
was stopped at its cap; this session starts with no verification retries used.

## Evidence

Commit `9b764ea5e55` passed fresh Stage-2 admission and replay. Stage 3 parsed all
664 frozen module surfaces without the former segmentation fault, then failed
closed with 1,347 HIR fatal records across 200 modules. The census contained six
unresolved types and seven unresolved names. The first cluster includes
`ProcessResult` in `src/std/nogc_sync_mut/io/process_ops.spl`, whose explicit
import must be registered before its return annotations are lowered. Stage 4
was unavailable and bootstrap refused seed fallback.

## Root owner

`src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl` still
crosses the staged boundary through nested parser aggregates:

- lines 210-227 read `imported_mod.imports[...]` and nested items during private
  facade/glob expansion;
- lines 234-317 read `module.imports[...]`, `imp.module`, `imp.items[...]`, and
  item aliases during primary import registration.

The scalar import-route projection added to `ModuleSurface` is currently used
only by later callable-dependency and re-export traversal, so it cannot protect
this earlier registration path.

## Unblock condition

Resolve the importing module's frozen `ModuleSurface` once and make both paths
consume only `import_target_*` and flattened `import_route_item_*` arrays, with
alignment/bounds failures closed. Preserve original module spelling in an
additional scalar route array if relative/module-only alias construction needs
it; use a scalar-safe span at this staged registration boundary. Add a source
contract forbidding `.imports[` and `.items[` in this file plus behavioral
coverage for explicit `ProcessResult`-shaped return types, aliases, module-only
imports, and globs. Verification must occur in a fresh bounded session.

## Implemented repair

`ModuleSurface` now freezes the authored module spelling alongside each
resolved target and flattened item route. Primary import registration resolves
the current physical surface once and consumes only those scalar arrays;
private facade/glob expansion does the same. Misalignment, out-of-range target
indices, or an indexed target without a canonical name fail closed. Import
diagnostics also use scalar counts instead of reopening parser aggregates.

The exact `ProcessResult` shape is covered by explicit and aliased structs used
only in return annotations. A source contract rejects `.imports[...]` and
`.items[...]` reads in the staged primary resolver. Fresh bootstrap evidence is
pending.
## Callable signature follow-up (2026-08-21)

Fresh verification proved scalar primary routes were necessary but not sufficient: Stage 3 reached HIR and reproduced the early Span/OptimizationLevel/ProcessResult cascade. The remaining cross-stage consumers indexed retained callable dictionaries and impl/trait method aggregates. Module surfaces now freeze aligned scalar signature, dependency, and impl-to-trait projections. Free functions, concrete impl methods, and trait methods consume only those projections; unsupported complex shapes deliberately register without an eager HIR function type. Bootstrap re-verification is pending.

## Flat AST parameter transport follow-up (2026-08-21)

The next bounded run died in Phase 2 while converting the first typed extern-heavy module. Kernel symbolization mapped the fault to `flat_ast_to_module` and a 48-byte aggregate copy selected through an invalid pointer. Both ordinary and extern parameter conversion constructed `Param.type_` with an inline conditional returning rich `Type` values; the ordinary path did the same for `Expr` defaults. Conversion now materializes stable typed locals before constructing `Param`, with exact extern and adjacent ordinary/default regressions.

Fresh verification then released all streaming surfaces and entered HIR, proving that repair. The original Span/Type cascade remained. Two surviving staged boundaries were identified: composite registration selected a scalar name but reopened the retained composite/field/Type dictionary payload, and qualified symbol bind/lookup depended on class-field Dict membership already known to mis-dispatch in self-hosted native code. Surfaces now freeze one reference-semantic scalar composite index, registration consumes only its kinds/field shapes/dependencies, and SymbolTable maintains scalar first-write qualified name/id indexes (including id zero) as the lookup authority.

The final bounded cycle moved composite projection emission into each live parser owner, eliminating the projection builder's Dict-value reopen, but Stage 3 again faulted after five released surfaces at `io_runtime.spl` parse-start. Because an earlier source layout with the stable Flat AST locals parsed the full closure, the remaining Phase-2 defect is source-layout-sensitive generated aggregate transport rather than a genuine syntax error in that module. No Stage-4 or push PASS is claimed.

# Stage-3 primary import resolution aggregate corruption (2026-08-21)

## Status

Open. The third bounded bootstrap verification cycle failed in Stage-3 HIR;
the session cap prohibits another fix/retry cycle.

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

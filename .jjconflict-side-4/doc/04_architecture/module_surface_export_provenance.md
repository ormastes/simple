<!-- codex-architecture -->
# Module Surface Export Provenance Architecture

## Status

Accepted for implementation: robust infrastructure, immediate safe provenance
slice. `ResolvedModuleGraph` remains phased future work.

## Context

`ModuleSurface` is the compact declaration boundary used by streaming Stage 4.
It preserves direct declarations and raw import/export syntax, but consumers
reconstruct re-export ownership through `find_reexport_source` and a separate
glob traversal. The duplicate, depth-capped algorithms amplify one missing
surface edge into hundreds of unresolved-type diagnostics.

## Decision

Add a compact semantic edge record in the existing 20.hir owner:

```simple
struct ModuleSurfaceExportOrigin:
    owner_surface_index: i64
    owner_name: text
    kind: text
    immediate_surface_index: i64
```

`ModuleSurface.reexports: Dict<text, ModuleSurfaceExportOrigin>` maps the public
name exposed by that surface to its canonical declaration. Direct declarations
stay in `callables`, `composites`, `enums`, `traits`, `type_aliases`, and
`constants`; they are not duplicated.

After `ModuleSurfaceBuilder` has registered all physical sources and aliases,
`module_surfaces_resolve_reexports` performs deterministic finalization:

1. Resolve module spellings to surface indices using one shared key resolver.
2. Seed direct explicit/aliased export edges.
3. Expand glob and transitive edges by stable fixpoint.
4. Coalesce candidates with the same canonical physical owner.
5. Reject cycles without a declaration, missing sources, and competing physical
   owners with structured context.

Streaming and retained constructors call this finalizer before publishing
`ModuleSurfacesByName`. HIR import registration uses a single
`module_surface_export_origin` lookup for explicit and glob imports. The old
chase remains temporarily behind a diagnostic fallback counter and is removed
after Stage 4 evidence is stable.

## Boundaries

- 10.frontend continues to own syntax. No parser representation migration is
  required in the immediate slice.
- 20.hir owns compact surface semantics and export provenance.
- 80.driver owns physical source discovery and logical aliases, not export
  meaning.
- 99.loader may later consume the resolved graph but does not become the HIR
  surface owner.
- Canonical authorization uses `ModuleSurface.canonical_path`; a spelling is
  never a principal.

This is a virtual capsule only in the architectural sense: provenance crosses
frontend metadata, HIR, and driver construction, but its stable contract stays
in the common HIR surface boundary. No MDSOC weaving/runtime adapter is needed.

## Cache and invalidation

The map is immutable for one compilation. Its validity is bound to each
surface's canonical path, content length/hash, and complete alias index. Any
source/export/import change rebuilds that surface set. No global persistent
cache is introduced in the immediate slice. A future serialized graph must key
nodes by physical identity plus content fingerprint and invalidate reverse
dependents on export-edge changes.

## Performance and observability

Finalization runs once per surface set and lookup replaces repeated recursive
scans. Debug counters record surfaces, export edges, fixpoint rounds, cycles,
ambiguities, legacy fallbacks, elapsed time, and retained bytes. NFR ceilings
are 5% Stage 4 HIR time and RSS regression.

## Phased future: ResolvedModuleGraph

Phase 2 introduces canonical `ResolvedModuleNode` and typed
`ResolvedModuleEdge` records for import, named export, alias export, and glob
export. Phase 3 attaches declaration IDs and visibility decisions. Phase 4
adds symbol-body closure so entry-closure discovery and HIR lowering consume one
graph. Only then should heuristic module-key fallback and duplicate closure
walkers be retired.

## Consequences and risks

Positive: canonical provenance, consistent named/glob behavior, deterministic
ambiguity, reduced diagnostic fan-out, and lower hot-path scanning.

Risks: native `Dict` pitfalls, nondeterministic key iteration, memory growth if
direct declarations are copied, alias cycles, and construction paths forgetting
finalization. Mitigations are bracket reads after `contains_key`, stable surface
order, re-export-only storage, explicit visited states, and construction-path
contract tests.

## References

- `doc/01_research/local/module_surface_export_provenance.md`
- `doc/02_requirements/feature/module_surface_export_provenance.md`
- `src/compiler/20.hir/hir_lowering/module_surface.spl`
- `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`
- `src/compiler/80.driver/driver_source_loading.spl`

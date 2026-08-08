# Module Surface Export Provenance Architecture — TLDR

Precompute compact re-export ownership once per `ModuleSurface` set so HIR no
longer repeatedly guesses declaration origins through depth-capped facade walks.

## Core Shape

- `ModuleSurface.reexports` maps public spelling to canonical owner surface,
  original name, kind, and immediate facade hop.
- Direct declaration dictionaries remain authoritative and are not copied.
- Finalize only after all physical aliases exist; coalesce same-file aliases and
  fail deterministically on cycles or competing physical owners.
- Explicit and glob imports consume the same lookup. Legacy chase is temporary,
  observable fallback only.

## Operational Notes

- hot path: average O(1) provenance lookup replaces repeated recursive scans.
- cache/index: compilation-local immutable map bound to source fingerprints.
- invalidation: any import/export/source change rebuilds the surface set.
- perf/RSS: no more than 5% regression; record edges, rounds, fallback count,
  elapsed time, and retained bytes.

## Open Next

- [Full architecture](module_surface_export_provenance.md)
- [Surface owner](../../src/compiler/20.hir/hir_lowering/module_surface.spl)
- [Test plan](../03_plan/sys_test/module_surface_export_provenance.md)
- Future: canonical `ResolvedModuleGraph`, then symbol-body entry closure.

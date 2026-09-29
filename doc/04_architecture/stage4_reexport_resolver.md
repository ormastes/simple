<!-- codex-design -->
# Stage4 re-export resolver architecture

`ModuleSurfacesByName` is the immutable graph capsule. It owns a
`ReexportResolverCache` and a `snapshot_generation` assigned when the builder
finishes resolving export origins. `HirLowering` receives that capsule and
uses its cache for completed root results. Its `reexport_active` map remains
transient DFS state and is cleared for every lookup/module transition.

This separates graph-scoped completed knowledge from lowering-scoped semantic
state. Construction of a new surface capsule creates a fresh cache and
generation, making invalidation structural rather than heuristic.

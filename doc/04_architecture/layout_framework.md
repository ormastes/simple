<!-- codex-design -->
# Layout Framework Architecture

## Decision

Implement a pure-Simple virtual capsule under `common.structural`: mapping, invalidation, and execution owner modules expose the versioned data contracts; `structural.layout` owns islands, profiles, SCC-wave scheduling, cost policy, and snapshots. Browser code remains a consumer and the current flat-array `layout()` result remains the CPU oracle.

<!-- sdn-diagram:id=layout-framework-architecture -->
```sdn
layout_framework: {
  inputs: [oracle_geometry, dependencies, dirty_mask, execution_profile],
  owners: {mapping: provenance, invalidation: dirty_edges, execution: costs_receipts, layout: islands_profiles_scheduler},
  outputs: [layout_snapshot, layout_of_edges, stage_receipt]
}
```

## Layers

1. `structural.mapping.contracts`: `MappingKind`, `MappingEdge`; no graph cache.
2. `structural.invalidation.contracts`: `DirtyMask`, `DependencyKind`, `DependencyEdge`; no propagation engine beyond what layout consumes.
3. `structural.execution.contracts`: `ExecutionMode`, `ExecutionProfile`, `CostEstimate`, `StageReceipt`.
4. `structural.layout.types`: snapshots, flat geometry, islands, faults, and receipts.
5. `structural.layout.profile`: `SpatialLayoutProfile`, serial CPU adapter, profile catalog, `TextMeasurePort`.
6. `structural.layout.scheduler`: SCC condensation, deterministic topological waves, dirty selection, bounded fixed points.
7. `structural.layout.engine`: full/incremental execution and end-to-end CPU/GPU cost choice.

## Invariants

- The capsule never imports browser, renderer, font-cache, atlas, runtime, or backend modules.
- A profile describes geometry semantics; it is not a resolver profile.
- All modes preserve the CPU snapshot. `hybrid_vector_gpu` is a dispatch receipt for eligible homogeneous batches; it never invents a second geometry algorithm in this framework lane.
- Inline measurement calls `TextMeasurePort`; failure or unsupported shaping selects CPU before execution.
- An SCC either converges within the positive cap or produces a non-convergence fault and CPU fallback receipt.
- Mapping and receipt arrays are output evidence, not hidden global state.

## Rejected

- Eight copied layout algorithms: duplicates the oracle and drifts.
- Browser types in common contracts: reverses layer ownership.
- Kernel-only GPU estimates: omits transfer/synchronization and falsely selects GPU.
- Mutable module-global scheduler state: interpreter persistence is unreliable and creates hidden coupling.


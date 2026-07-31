<!-- codex-design -->
# Layout Framework Architecture

## Decision

Implement a pure-Simple virtual capsule under `common.structural`: mapping, invalidation, and execution owner modules expose the versioned data contracts; `structural.layout` owns islands, profiles, SCC-wave scheduling, cost policy, and snapshots. Browser code remains a consumer; the current flat-array `layout()` is both the production CPU implementation and the independent test oracle.

<!-- sdn-diagram:id=layout-framework-architecture -->
```sdn
layout_framework: {
  inputs: [consumer_snapshot, dependencies, dirty_mask, execution_profile, cpu_port, gpu_port],
  owners: {mapping: provenance, invalidation: dirty_edges, execution: costs_receipts, layout: islands_profiles_scheduler_ports},
  outputs: [boxes, fragments, line_boxes, overflow, layout_of_edges, stage_receipt]
}
```

## Layers

1. `structural.mapping.contracts`: `MappingKind`, `MappingEdge`; no graph cache.
2. `structural.invalidation.contracts`: `DirtyMask`, `DependencyKind`, `DependencyEdge`; no propagation engine beyond what layout consumes.
3. `structural.execution.contracts`: `ExecutionMode`, `ExecutionProfile`, `CostEstimate`, `StageReceipt`.
4. `structural.layout.types`: snapshots, flat geometry, islands, faults, and receipts.
5. `structural.layout.profile`: `SpatialLayoutProfile`, profile catalog, family-aware `TextMeasurePort`, and per-island costs.
6. `structural.layout.scheduler`: SCC condensation, deterministic topological waves, dirty selection, and the positive iteration cap.
7. `structural.layout.execution_port`: `LayoutExecutionRequest`, `LayoutIterationResult`, and `LayoutExecutionPort`; consumer-owned CPU/GPU implementations perform geometry work.
8. `structural.layout.engine`: full/incremental orchestration, convergence comparison, cost choice, oracle verification, and honest receipts.

## Invariants

- The capsule never imports browser, renderer, font-cache, atlas, runtime, or backend modules.
- A profile describes geometry semantics; it is not a resolver profile.
- `layout_choose_backend` returns a candidate only. `LayoutSnapshot.backend = hybrid_vector_gpu` requires a successful execution-port result with submission, synchronization, device readback, and exact oracle equality.
- `LayoutNodeSemantics` carries authored topology, typed block/flex/grid constraints, typed position offsets (`auto` is explicit unset), and per-axis overflow policy. CPU-oracle boxes are snapshot-level verification evidence and are never part of the packed device payload.
- The browser-owned CUDA port admits exact fixed-size one-level block/flex/grid, absolute, and vertical-scroll islands with an empty box model. It computes geometry, clip boxes, and scroll extents from semantic device inputs; sticky positioning, non-pixel offsets, and wider shapes reject before upload.
- Its layout receipt cannot satisfy Draw IR reconciliation R7, R8, or R9;
  those rows require canonical `DrawIrComposition -> RenderBackend.submit_batch`
  execution and device-origin readback evidence.
- Inline measurement sends node id, content, family, size, and language through `TextMeasurePort`; unavailable or mismatched shaping selects CPU before execution.
- Cyclic SCCs execute iterations and compare geometry hashes. A stable hash converges; reaching the positive cap produces a non-convergence fault and CPU fallback receipt.
- CPU algorithms remain consumer-owned. The browser CPU port adapts the current flat-array renderer; the common capsule never copies browser layout logic.
- The v1 CPU selection seam recomputes the canonical root and filters selected outputs. It preserves correctness and incremental receipt/merge scope, but does not claim reduced CPU layout work.
- Mapping and receipt arrays are output evidence, not hidden global state.

## Rejected

- Eight copied layout algorithms: duplicates the oracle and drifts.
- Browser types in common contracts: reverses layer ownership.
- Treating cost selection as GPU execution: emits false backend evidence.
- Fixture-declared convergence counts: tests the fixture, not a fixed point.
- Kernel-only GPU estimates: omits transfer/synchronization and falsely selects GPU.
- Mutable module-global scheduler state: interpreter persistence is unreliable and creates hidden coupling.

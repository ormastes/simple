<!-- codex-design -->
# Layout Framework Detail Design

## Data

- IDs and hashes use stable integer/text fields in v1; every shared contract carries `contract_version = 1` through constructors.
- `LayoutNodeInput` is flat and ordered: stable id, parent id, profile id, boundary flags, typed box/flex/grid/position/overflow semantics, dirty mask, work estimate, and text-measure requirement.
- `LayoutInputSnapshot` owns nodes, dependencies, invalidated ids, family-aware text requests, retained geometry/artifacts, optional independent oracle evidence, execution profile, and fixed-point cap.
- `LayoutSnapshot` owns boxes, fragments, line boxes, overflow, islands, waves, visited ids, `LayoutOf` edges, fault, and `StageReceipt`.
- `LayoutExecutionRequest` owns the selected islands/waves, prior iteration output, and execution profile. `LayoutIterationResult` owns output geometry plus submission/synchronization/readback facts.

## Algorithms

1. Discover islands in input order. The root and nodes establishing formatting/containment boundaries start islands; descendants inherit the nearest island.
2. Sum node work into island estimates. Compute and record one CPU/GPU cost per island, then sum only the selected homogeneous batch.
3. Condense SCCs, sort component members and ready components by lowest island id, and emit topological waves.
4. Full mode visits every island. Incremental mode selects dirty islands plus dependency-required islands only; clean independent islands are copied from retained geometry, never oracle evidence.
5. Execute each cyclic wave through the chosen port. Compare ordered geometry hashes after every iteration; stop on equality or return `non-convergent` at `fixed_point_cap`.
6. Total GPU latency is kernel + scheduling + upload + readback + synchronization. Select a GPU candidate only when every island is in the explicitly admitted block/flex/grid/absolute/scroll subset, the batch is homogeneous, text is absent, and the summed GPU total is lower than CPU.
7. Invoke the GPU port only when independent oracle evidence is present for a candidate. Accept it only when submission, synchronization, device readback, and exact parity succeed; otherwise execute the CPU port and record the concrete fallback reason.
8. Pack only `LayoutNodeSemantics`, viewport values, and grid tracks for device execution. Keep oracle geometry and artifacts host-side for post-readback comparison. The fixed CUDA slice accepts positive fixed-pixel one-level block/flex/grid roots, absolute children with pixel offsets, and vertical auto/scroll roots with an empty box model. Sticky, percentage offsets, nested descendants, and compound policies pre-reject.
9. Run ordered geometry, absolute-offset, and overflow kernels. Read back boxes plus clip/scroll fields and accept them only under exact oracle parity.
   This layout-only receipt cannot close Draw IR reconciliation R7–R9; those
   gates require canonical composition submission and device-origin pixels.
10. Emit one `LayoutOf` mapping per visited output box and retain fragments, line boxes, and overflow from the accepted execution result.
11. The browser CPU port runs canonical root layout, emits only selected-island outputs, merges clean retained outputs, and falls back to canonical full CPU layout if adapter or framework execution faults.

## Public API

- `layout_discover_islands(input)`
- `layout_schedule_waves(islands, dependencies, cap)`
- `layout_run_full(input, text_port)`
- `layout_run_incremental(input, text_port)`
- `layout_run_full_with_ports(input, text_port, cpu_port, gpu_port)`
- `layout_run_incremental_with_ports(input, text_port, cpu_port, gpu_port)`
- `layout_choose_backend(islands, profile)`
- per-island estimates in `LayoutSnapshot.island_costs`
- traits `SpatialLayoutProfile`, `TextMeasurePort`, and `LayoutExecutionPort`

## Errors

Invalid cap, missing parent/island, dependency endpoint, text measurement, unsupported GPU profile, missing execution port, failed submission/synchronization/readback, oracle mismatch, and non-convergence are explicit result/fault fields. Safe cases select CPU with a reason; malformed inputs do not silently fabricate geometry.

## Observability

Receipts expose mode/backend, visited island ids, fallback reason/count, input/output deterministic hashes, item counts, estimated CPU/GPU latency, transfer bytes, synchronization points, iteration count, and convergence.

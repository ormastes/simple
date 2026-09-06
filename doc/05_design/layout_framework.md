<!-- codex-design -->
# Layout Framework Detail Design

## Data

- IDs and hashes use stable integer/text fields in v1; every shared contract carries `contract_version = 1` through constructors.
- `LayoutNodeInput` is flat and ordered: stable id, parent id, profile id, boundary flags, geometry oracle box, dirty mask, estimated work, and text-measure requirement.
- `LayoutInputSnapshot` owns nodes, dependencies, invalidated ids, execution profile, and fixed-point cap.
- `LayoutSnapshot` owns boxes, islands, waves, visited ids, `LayoutOf` edges, fault, and `StageReceipt`.

## Algorithms

1. Discover islands in input order. The root and nodes establishing formatting/containment boundaries start islands; descendants inherit the nearest island.
2. Sum node work into island estimates and retain dependency edges between island roots.
3. Condense SCCs, sort component members and ready components by lowest island id, and emit topological waves.
4. Full mode visits every island. Incremental mode selects dirty islands plus dependency-required islands only; clean independent islands are copied from the prior/oracle snapshot.
5. Cyclic components iterate at most `fixed_point_cap`. A fixture-provided change count models convergence; exhaustion returns `non-convergent` and CPU fallback.
6. Total GPU latency is kernel + scheduling + upload + readback + synchronization. Select GPU only when every island is block/flex/grid, the batch is homogeneous, text is absent, and GPU total is lower than CPU.
7. Arrangement reuses oracle geometry. Verification compares stable id and exact x/y/width/height fields and emits one `LayoutOf` mapping per visited output box.

## Public API

- `layout_discover_islands(input)`
- `layout_schedule_waves(islands, dependencies, cap)`
- `layout_run_full(input, text_port)`
- `layout_run_incremental(input, text_port)`
- `layout_choose_backend(islands, profile)`
- trait `SpatialLayoutProfile`; trait `TextMeasurePort`

## Errors

Invalid cap, missing parent/island, dependency endpoint, text measurement, unsupported GPU profile, and non-convergence are explicit result/fault fields. Safe cases select CPU with a reason; malformed inputs do not silently fabricate geometry.

## Observability

Receipts expose mode/backend, visited island ids, fallback reason/count, input/output deterministic hashes, item counts, estimated CPU/GPU latency, transfer bytes, synchronization points, iteration count, and convergence.


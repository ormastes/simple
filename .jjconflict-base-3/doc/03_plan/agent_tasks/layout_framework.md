# Layout Framework Agent Tasks

## Shared Contract

- Interfaces: `LayoutInputSnapshot`, `LayoutSnapshot`, `LayoutIsland`, `SpatialLayoutProfile`, `TextMeasurePort`, `LayoutExecutionPort`, `LayoutExecutionRequest`, and `LayoutIterationResult`.
- Manual steps: `Discover layout islands`; `Schedule dirty layout waves`; `Measure and arrange profiles`; `Verify geometry and receipts`.
- Checkers: `layout_fixture_snapshot`, `expect_layout_geometry`, `expect_dirty_island_receipts`, `expect_bounded_fixed_point`.
- No placeholder is accepted; temporary bodies fail explicitly and are removed before merge.

## Lanes

| Lane | Owned files | Deliverable |
|---|---|---|
| contracts | `src/lib/common/structural/{mapping,invalidation,execution}/**` | v1 contract subset + focused tests |
| profiles | `src/lib/common/structural/layout/{types,profile,text_measure}.spl` | snapshots, profile catalog, family-aware text boundary, per-island costs |
| scheduler | `src/lib/common/structural/layout/scheduler.spl` | islands and SCC waves |
| execution | `src/lib/common/structural/layout/{execution_port,engine}.spl` | consumer ports, convergence, incremental execution, proof-qualified receipts |
| browser CPU port | `src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/**` | current-layout adapter, fragments/line/overflow parity |
| browser GPU port | consumer-owned GPU layout files | block/flex/grid submission, synchronization, readback, oracle comparison |
| evidence | layout unit/system specs and generated manual | AC/REQ traceability and operator-readable flow |
| docs review | layout framework docs only | freshness and manual-quality audit |

Merge owner and final highest-capability reviewer: root Codex agent. Lower-model sidecars may implement bounded disjoint lanes; the root reviewer accepts execution claims, interfaces, generated-manual quality, exclusions, and done marks.

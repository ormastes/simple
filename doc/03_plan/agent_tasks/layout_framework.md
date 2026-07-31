# Layout Framework Agent Tasks

## Shared Contract

- Interfaces: `LayoutInputSnapshot`, `LayoutSnapshot`, `LayoutIsland`, `SpatialLayoutProfile`, `TextMeasurePort`.
- Manual steps: `Discover layout islands`; `Schedule dirty layout waves`; `Measure and arrange profiles`; `Verify geometry and receipts`.
- Checkers: `layout_fixture_snapshot`, `expect_layout_geometry`, `expect_dirty_island_receipts`, `expect_bounded_fixed_point`.
- No placeholder is accepted; temporary bodies fail explicitly and are removed before merge.

## Lanes

| Lane | Owned files | Deliverable |
|---|---|---|
| contracts | `src/lib/common/structural/{mapping,invalidation,execution}/**` | v1 contract subset + focused tests |
| profiles | `src/lib/common/structural/layout/{types,profile,text_measure}.spl` | snapshots, catalog, CPU/text boundary |
| scheduler | `src/lib/common/structural/layout/{scheduler,engine}.spl` | islands, SCC waves, incremental/cost execution |
| evidence | layout unit/system specs and generated manual | AC/REQ traceability and operator-readable flow |
| docs review | layout framework docs only | freshness and manual-quality audit |

Merge owner and final highest-capability reviewer: root Codex agent. Lower-model sidecars may implement bounded lanes; the root reviewer accepts interfaces, generated-manual quality, exclusions, and done marks.


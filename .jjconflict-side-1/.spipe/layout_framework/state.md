# Feature: layout-framework

## Raw Request
`$sp_dev with small agents team impl layout_framework_plan.md`

## Task Type
feature

## Refined Goal
Implement the complete generic spatial-layout framework defined by `doc/03_plan/platform/structural_compute/layout_framework_plan.md`, preserving CPU geometry while adding bounded incremental island scheduling and cost-qualified GPU profile dispatch.

## Acceptance Criteria
- AC-1: Public contracts exist for `LayoutInputSnapshot`, `LayoutSnapshot`, `LayoutIsland`, `SpatialLayoutProfile`, and `TextMeasurePort`, and layout consumes the frozen DirtyMask, dependency-edge, MappingGraph, stage-receipt, and execution-profile contracts without defining a ResolveProfile substitute.
- AC-2: Formatting-context and containment boundaries deterministically partition identical input snapshots into identical layout islands with recorded cost estimates.
- AC-3: The initial block, inline, flex, grid, table, absolute/sticky, scroll, and replaced profiles support discover, estimate, measure, arrange, and verify through the shared profile contract; inline measurement uses `TextMeasurePort` and never approximates shaping for GPU eligibility.
- AC-4: The dependency scheduler represents intrinsic-size, containing-block, percentage, baseline, and track/column constraints, condenses strongly connected components, emits topological waves, and terminates cyclic work through an explicit fixed-iteration cap or a non-convergence fault.
- AC-5: A serial CPU adapter produces fragment/box geometry identical to the current CPU pipeline for block, flex, grid, table, absolute, and scroll fixtures.
- AC-6: Incremental layout produces the same snapshot as full layout for identical inputs, visits only DirtyMask-invalidated islands, and records the visited-island and `LayoutOf` provenance in receipts/mapping edges.
- AC-7: Cost estimates include scheduling, transfer, and synchronization overhead; `hybrid_vector_gpu` dispatches only a homogeneous block/flex/grid batch whose recorded estimate beats CPU, while small pages, inline layout, unsupported profiles, and non-convergent work fall back to CPU.
- AC-8: Focused unit and modern SSpec coverage directly asserts geometry, deterministic islands, dependency-wave order, bounded convergence, dirty-island visitation, MappingGraph edges, CPU fallback, and both below/above-crossover dispatch decisions without placeholder or boolean-wrapper assertions.
- AC-9: Research, selected feature/NFR requirements, architecture/detail design, system-test plan, cooperative agent-task plan, executable SSpec, generated operator-readable manual, and relevant structural-compute guide references are current and trace every AC to implementation and evidence.
- AC-10: Focused checks, changed-file lint, duplication check, generated-spec layout guard, and working/staged direct-env runtime guards pass once; final high-capability review confirms every plan phase and acceptance row has authoritative evidence.

## Scope Exclusions
- Browser-specific manager integration remains owned by `web_layout_manager_plan.md`.
- A new resolver profile, a second shaping engine, and approximation of text shaping are excluded.
- GPU text layout and non-homogeneous GPU batches are excluded until independently verified.

## Cooperative Review
- Small-agent lanes: contract/current-pipeline research; island/dependency scheduler implementation; profile/CPU adapter implementation; cost/GPU-dispatch implementation; SSpec/manual and documentation audit.
- Merge owner: root Codex agent in the `layout_framework` lane.
- Final reviewer: root Codex agent at normal/highest available capability.
- Shared interfaces: `LayoutInputSnapshot`, `LayoutSnapshot`, `LayoutIsland`, `SpatialLayoutProfile`, `TextMeasurePort`; reuse existing `DirtyMask`, dependency edge, `MappingGraph`, stage receipt, and execution-profile types.
- Manual `step("...")` flow: `Discover layout islands`; `Schedule dirty layout waves`; `Measure and arrange profiles`; `Verify geometry and receipts`.
- Setup/checker helpers: `layout_fixture_snapshot`, `expect_layout_geometry`, `expect_dirty_island_receipts`, `expect_bounded_fixed_point` (reuse equivalents if already present).
- Fail-fast placeholders: none permitted; any temporary helper must use `assert(false)` or `fail(...)` and be removed before merge.
- Generated-manual review owner: root Codex agent after the spec lane produces the first mirrored manual.

## Research Summary

### Existing Code
- `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md` §§6/9/17/21 — authoritative pseudocode; source contracts are missing.
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl` — canonical flat-array CPU geometry oracle; dirty in another lane.
- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` — existing shaping/metric owner; framework must call through a port.

### Reusable Modules
- Current browser `layout()`/`LayoutResult` is the one adapter target; legacy BeLayoutBox is excluded.
- Structural owner modules will hold only the contract subset this plan consumes.

### Domain Notes
- W3C formatting-context/containment boundaries justify islands while preserving cross-boundary sizing edges; Tarjan SCC condensation provides bounded wave scheduling.

### Open Questions
- NONE

<!-- sdn-diagram:id=layout-framework-context -->
```sdn
layout_framework: { consumes: [mapping, invalidation, execution, text_measure], oracle: browser_cpu_layout, emits: [layout_snapshot, layout_receipt] }
```

## Requirements
- REQ-001..REQ-003 (AC-1..AC-3): contracts, islands, profiles, text port — area: `src/lib/common/structural/`.
- REQ-004..REQ-005 (AC-4): SCC waves and bounded fixed points — area: `src/lib/common/structural/layout/`.
- REQ-006..REQ-007 (AC-5..AC-6): CPU/incremental parity, LayoutOf, receipts — areas: framework plus consumer adapter.
- REQ-008 (AC-7..AC-8): end-to-end cost-qualified dispatch and focused evidence — areas: framework and tests.
- NFR-001..NFR-008 (AC-9..AC-10): determinism, termination, fidelity, isolation, current artifacts, one-pass gates.

## Architecture Summary

- Virtual capsule: structural mapping, invalidation, execution, and layout owner modules with no browser/runtime imports.
- Shared interfaces: `LayoutInputSnapshot`, `LayoutSnapshot`, `LayoutIsland`, `SpatialLayoutProfile`, `TextMeasurePort`.
- One serial CPU-oracle boundary feeds exact flat geometry; profiles never duplicate layout algorithms.
- Deterministic SCC condensation emits topological waves; cyclic work is capped or faults.
- Cost policy admits only homogeneous block/flex/grid batches after transfer and synchronization costs.
- Browser conversion is a consumer adapter owned by `web_layout_manager_plan.md`; conflicted browser files remain untouched.

## Design Artifacts

- `doc/04_architecture/layout_framework.md`
- `doc/05_design/layout_framework.md`
- `doc/03_plan/sys_test/layout_framework.md`
- `doc/03_plan/agent_tasks/layout_framework.md`
- `doc/07_guide/platform/structural_compute/layout_framework.md`

## Implementation

- Contracts: `src/lib/common/structural/{mapping,invalidation,execution}/`.
- Framework: `src/lib/common/structural/layout/{types,profile,scheduler,engine}.spl` and public barrel.
- Evidence source: focused unit and system specs listed below.
- Cooperative review: scheduler, profile, engine, and spec lanes merged; root reviewed interface ownership, homogeneous GPU admission, DirtyMask/MappingGraph/StageReceipt integration, and no-browser/runtime imports.
- Documentation freshness: layout research, selected requirements, architecture, detail design, test/agent plans, guide, and TLDR companions updated. Workflow/tooling command/skill docs are N/A because no workflow or tool contract changed.

## Phase
implement-source-done

## Log
- dev: Created state file with 10 acceptance criteria (type: feature).
- research: Found one canonical CPU oracle, one text owner, no implemented frozen contracts, and eight selected requirements.
- arch: Designed seven owner modules, one CPU-oracle boundary, deterministic SCC waves, and cost-qualified dispatch.
- specs: Added focused unit and system SSpec coverage at the two planned executable paths. The public `common.structural.layout` barrel is frozen around the five designed APIs plus minimal value constructors; `layout_execution_profile` records kernel, scheduling, transfer, and synchronization inputs, and `layout_node` records required fixed-point iterations.
- specs: Coverage directly asserts constructors/versioning, deterministic islands, SCC wave order, cap exhaustion, malformed dependencies, honest backend cost, CPU fallbacks, full/incremental oracle equality, visited islands, `LayoutOf` mappings, and receipt hashes. The system manual shape is one visible four-step primary flow using exactly the frozen phrases, followed by folded edge behavior for small/text/non-convergent work.
- specs-alignment: Reviewed every file under `src/lib/common/structural/`. The two specs match the concrete barrel's constructor signatures, v1 fields, `LayoutTextMeasureResult`, `SpatialLayoutProfile`, and `TextMeasurePort`; the primary GPU fixture is homogeneous block layout as required by the design.
- implement: Added the five behavior APIs, eight-profile serial catalog, concrete DirtyMask/MappingGraph/ExecutionProfile/CostEstimate/StageReceipt contracts, deterministic SCC waves, bounded fixed points, exact oracle snapshots, incremental receipts, and cost-qualified homogeneous GPU dispatch.
- verification-blocker: The current pure-Simple wrapper reports `error: unknown command 'check'`, `error: unknown command 'test'`, and `error: unknown command 'spipe-docgen'`; a separate full bootstrap is active. No mirrored manual or runtime PASS is claimed in this checkpoint.
- audits: `layout_framework_contract_audit` confirms AC-1..AC-3 (contracts, islands, profiles, and profile catalog). `layout_framework_engine_audit` validates incremental dependency propagation and marks the producer→consumer directional fix done. `layout_framework_test_docs_audit` confirms AC-8..AC-10 coverage mapping for unit/system specs, fallback proof cases, GPU proof-unavailable gating, and generated-spec visibility.

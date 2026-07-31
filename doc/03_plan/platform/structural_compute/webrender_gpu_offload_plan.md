# WebRender GPU Offload Plan (remaining WebScene lanes)

**Date:** 2026-07-31 · **Status:** Proposed
**Parent:** `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` — this
plan indexes its remaining work groups; that document stays authoritative for
contracts, ownership and gates. Parser/style/layout/link/placement halves are
covered by the sibling lane plans in this directory.

## Scope

Everything in the GPU WebScene lane not owned by a sibling plan:

| Group | Content |
|---|---|
| W1 | `@gpu_event` GPU-safe Simple script compiler (HIR effect/bound analysis → GpuEventIR → ProcessingIR → CPU oracle + SPIR-V/CUDA/MSL/DXIL/SIMD) |
| W2 | GPU event core: input ring, coalescing, hit query, capture/target/bubble, deterministic mutation journal, host-effect ring |
| W6A/W6B | GPU image codecs (WebP/PNG staged decoders, libwebp oracle) and video surfaces (Vulkan Video VP9/AV1, zero-copy YUV) |
| W7/W8* | WebScene scheduler + platform adapters (Vulkan/Metal/DX/CUDA/WebGPU tiers 0–2) |
| W9 | Host services + SimpleOS bridge (effect services, IVSHMEM, fault restart) |
| W10/W11 | Web integration (feature flags, shadow → candidate → promotion) + evidence |
| I1–I12 | DrawIR v3 program: contract, capacity/no-realloc pools, typed tables, diff/patch, CPU oracle sinks, count/scan/emit + Prepared2D, hit index, cache, v2/v3 adapters, execution backends, Engine2D integration, evidence |

## Structural-compute bindings (normative)

- WebScene device pools = Object VM arenas (gpu_mmu lane contracts); no
  private placement layer.
- Mutation journal commit = MutationIR snapshot semantics; scene generation is
  a `SnapshotId`.
- DrawIR v3 `SourceProvenanceTable` = MappingGraph edges (`PaintOf`,
  `HitRegionOf`).
- Invalidation frontiers = DirtyMask + selector-feature model shared with the
  html_css_parser lane.
- DrawIR v3 is a packed encoding of the one shared display list
  (`DrawIrComposition` — DrawIR v2); it is not a second display-list format.
  The WebIR rejection stands: `doc/03_plan/ui/webir_drawir_optimization.md`
  §Decision. Table/pool implementations follow ADR-004 write-back semantics
  (`doc/04_architecture/adr/ADR-004-indexed-access-value-semantics.md`).

## Ownership and ordering

Owned paths, feature flags, waves (WAVE 0–5), dependency graph, and acceptance
gates are defined in the parent plan §10–§14 and are not duplicated here.
Ownership ledger: `doc/03_plan/agent_tasks/gpu_web_scene/ownership.sdn`.

Implementation ordering (parent §15): DrawIR v3 foundation (I1–I3) and the
`@gpu_event` compiler + event transaction model (W1/W2) first; full GPU
DOM/style/layout/media stages connect only after the first vertical slice
(panel/button/flex/custom-property fixture on Vulkan) passes its proofs:

```text
no allocator call after startup · no pixel readback · no per-widget submission
CPU oracle state/layout/IR/pixel parity · clean device-loss recovery
flag-off byte-identical to current behavior
```

## Acceptance

The parent plan's gates apply verbatim (§14): byte-matching mutation
journals, canonical serialization parity, semantic checksums, fail-closed
capacity overflow, no hidden SoftwareBackend calls, and promotion only on
measured p50/p95 event-to-present improvement including transfer +
synchronization cost.

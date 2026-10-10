# variants/ Manifest

## 2026-10-11 sparse variation policy

This directory remains the resolver-only overlay root selected by `config/var.sdn`. See the [integrated variation design](../doc/05_design/compiler/simd_gpu_sosix_variation_final_2026-10-10.md) and [Item 5 plan](../doc/03_plan/compiler/perf/runtime_optional_provider_binary_size_optimization_plan_2026-09-02.md#2026-10-11-selected-variation-migration).

Keep instruction encoders and native providers in their layer-owned directories. An index describes them; it does not relocate or copy them. Generic pointer-width/endian differences are layout inputs, not copied `bits32/` and `bits64/` algorithm trees. Planned scoped-slot applicability, unrelated-shadow rejection, legacy SIMD-root normalization and generated indexes require resolver/parser/cache enforcement. Existing policy text alone does not implement that enforcement; historical inventories below are not exhaustive current support lists.

Module-variant-override overlays. Selected by explicit `variant:`/`platform:`
build configuration to override a base seam file (e.g.
`src/lib/nogc_sync_mut/target_ext.spl`,
`src/lib/gc_async_mut/gpu/engine2d/renderer_select.spl`) with a fixed,
target-specific implementation. Current configuration/manifest machinery also supports automatic selection; the former assertion that default/`auto` never selects overlays is superseded. Selected roots precede defaults and manifest order resolves current ties. Scoped ownership enforcement remains pending; the workspace-root guard is not proof of resolver policy enforcement.

## Allowed Entries

| Entry | Description |
|---|---|
| `__init__.spl` | Package marker |
| `platform` | Platform build-extension overlays (`linux`/`mac`/`windows`) for `nogc_sync_mut/target_ext.spl` |
| `ui` | UI renderer-selection overlays (`cpu`/`metal`/`vulkan`/`webgpu`) for `gpu/engine2d/renderer_select.spl` |
| `hw` | Hardware-specific overlays listed by the current manifest; selection does not itself prove execution support |
| `lib.crypto` | Crypto variation group in the current manifest/configuration; retain its existing resolver identity |
| `FILE.md` | This manifest |

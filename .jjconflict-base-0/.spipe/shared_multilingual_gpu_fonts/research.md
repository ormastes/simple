# Shared Multilingual GPU Fonts — Research State

## Research Summary

- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:42-389` is the canonical renderer/cache.
- `src/lib/skia/feature/shaper/shaper.spl:1-633` and `feature/text/bidi.spl:1-230` are reusable Pure Simple shaping foundations.
- `src/lib/common/encoding/font_registry.spl:1-359` has an implicit/stale ten-language set and incomplete provenance.
- `src/compiler/70.backend/backend/gpu_portable_compute.spl:241-758` is the single reusable Simple GPU emitter.
- `src/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl:15-369` supplies the honest evidence ladder.
- Engine2D has a TTF payload adapter; game/3D text has atlas metadata but no real texture.
- Metal alone currently performs genuine fixed-5x7 GPU atlas composition.
- Full findings: `doc/01_research/{local,domain}/shared_multilingual_gpu_fonts.md`.

### Open Questions

- NONE; material choices are escalated as mandatory feature/NFR options.

<!-- sdn-diagram:id=shared_multilingual_gpu_fonts.research -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=shared_multilingual_gpu_fonts.research hash=sha256:auto render=ascii
@layout dag
@direction LR
FontManifest -> FontRenderer
PureSimpleShaper -> FontRenderer
FontRenderer -> PortableGpuEmitter
FontRenderer -> CpuOracle
PortableGpuEmitter -> Engine2D
PortableGpuEmitter -> Engine3D
Engine2D -> DeviceEvidence
Engine3D -> DeviceEvidence
```
</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=shared_multilingual_gpu_fonts.research hash=sha256:auto
# run: simple md-diagram-update
```
</details>
<!-- sdn-diagram:end -->

## Requirements

| Requirement | ACs | Area |
|---|---|---|
| Pin ranking and prove shaping coverage | AC-1, AC-2 | registry/shaper/fixtures |
| License-audit every font | AC-3 | manifest/assets/notices |
| Share one glyph-run/atlas contract | AC-4, AC-7, AC-8 | text layout/2D/3D |
| Reuse the Pure Simple GPU emitter | AC-5, AC-13 | portable compute |
| Prove emission through native present separately | AC-6 | dispatch/backend evidence |
| Bound/invalidate caches and meet selected NFRs | AC-9, AC-10 | caches/perf |
| Keep SSpec manuals and process docs current | AC-11, AC-12 | tests/guides/skills |
| Preserve dirty work and compatibility adapters | AC-7, AC-14 | integration lane |

## Cooperative Review

`font_local_reuse`, `font_license_coverage`, and `font_gpu_emission` were accepted after primary review against repository paths and authoritative sources.

## Current Implementation Addendum — 2026-07-13

The summary above records the pre-selection baseline. Current source bundles
the selected 16 candidates, owns the exact 10×10 sparse matrix, emits the shared
versioned font-atlas program, and routes canonical `FontRenderBatch` material
through Engine2D CUDA/Metal/OpenCL/Vulkan adapters and the optional Vulkan
Engine3D adapter. Web semantic/layout, GUI, shared WM, and the SimpleOS desktop
witness lower through Draw IR/Engine2D. The legacy SimpleOS WM still paints
direct bitmap/vector text pending a frame-level Draw IR migration. Device
execution, retained SimpleOS pixels, performance, and
canonical docgen are still required before promotion.

## Phase

research-done-selection-complete

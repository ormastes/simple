<!-- codex-design -->
# Shared Multilingual GPU Fonts Architecture

Status: design for selected `L2+C1+S1+F1+R1+P1+G1`, NFR A.

## Decision

Extend the existing `FontRenderer`; do not create another font stack. CPU code
owns manifest validation, shaping, glyph rasterization, fallback, atlas updates,
and cache identity. Simple-emitted GPU programs only compose the resulting alpha
atlas. Engine2D and Engine3D consume one immutable `FontRenderBatch` and retain
their existing public entrypoints.

This is a small MDSOC extraction: the shared run/atlas values sit at the common
text-layout node; engine adapters remain sibling-private. There is no runtime
plugin interface, renderer factory, or new native dependency.

## Current state

| Existing path | Kept responsibility |
|---|---|
| `src/lib/common/encoding/font_registry.spl` | Static pinned language/category catalog; nine simple-script families are accepted for exact tuples while seven complex/emoji candidates remain gated. |
| `src/lib/common/encoding/font_cldr_rank.spl` | Targeted, exact-arithmetic CLDR ranking core with fixture evidence; validating XML input and pinned-source replay remain gates. |
| `src/lib/common/encoding/sfnt.spl` | Neutral sfnt directory/fvar owner and typed default-`glyf` preflight shared by both production loaders; the old Skia parser modules are compatibility re-exports. |
| `src/lib/common/gpu/font_atlas_composite.spl` | Shared atlas subrect/color material plus exact OpenCL and Metal kernel sources used by compiler emission and runtime adapters. |
| `src/lib/nogc_sync_mut/text_layout/font_types.spl` | Canonical shared values; gains `FontGlyphRun`, `FontRenderQuad`, and `FontRenderBatch`. `FontGlyphRun` carries the exact revocable face handle/generation pair plus logical codepoint clusters; consumers validate liveness and never dereference the handle directly. |
| `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` | Canonical renderer, glyph cache, CPU payload; gains `prepare_text`, the bound glyph-run adapter, and fail-closed sfnt preflight before native loading. |
| `src/lib/skia/feature/shaper/shaper.spl` and `src/lib/skia/feature/text/bidi.spl` | Existing Pure Simple shaping/BiDi owners; exact per-fallback-face `OtFont` binding plus glyph/source/cluster/language/current-placement metadata are present. No-feature Latin/Han/Cyrillic corpus acceptance passed; complex/emoji shaping, GSUB/GPOS, canonical language handling, and full BiDi remain gated. |
| `src/compiler/70.backend/backend/gpu_portable_compute.spl` | Portable CUDA/HIP/OpenCL/Metal/WGSL artifacts; gains the atlas-composite emitter. |
| `src/compiler/70.backend/backend/gpu_generated_2d_contract.spl` | Version, symbol, compile-plan, and artifact evidence. |
| `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | Existing `load_font`/`draw_text` adapter and backend submission. |
| `src/lib/gc_async_mut/gpu/engine3d/engine.spl` | Texture/pipeline/draw owner; gains only HUD/world text entrypoints. |
| `src/lib/gc_async_mut/gpu/engine2d/opencl_session.spl` | Exact OpenCL font ABI binding, offset-aware atlas writes, and runtime-selected-workgroup launch; other target adapters remain gates. |

Compatibility re-export trees continue to expose the canonical
`nogc_sync_mut.text_layout` values. Generated copies must not acquire private
implementations.

## To-be layers and encapsulation

1. **Pinned data:** CLDR inputs, generated language manifest, unchanged font
   binaries, and notices. Validation fails before any font becomes selectable.
2. **Common catalog:** `common.encoding.font_registry` exposes immutable lookup
   results. Asset parsing, hashes, and fallback policy are tree-private.
3. **Shared text material:** canonical `text_layout.font_types` and
   `FontRenderer` own shaped identity, CPU raster material, atlas generation,
   cache statistics, and fallback. Rasterizer/shaper internals stay tree-private.
4. **Program artifacts:** the existing compiler portable-compute contract emits
   CUDA/HIP/OpenCL/Metal/WGSL font source and compile plans. A font-specific
   Vulkan SPIR-V artifact is still required; neither emission path may claim
   execution.
5. **Engine adapters:** Engine2D and Engine3D translate a `FontRenderBatch` into
   their own texture, sampler, transform, depth, submit, fence, and readback
   operations. Neither engine reads the other's private state.

### Common relative tree nodes

- `common/encoding/font_registry.spl`: validated catalog lookup.
- `nogc_sync_mut/text_layout/font_types.spl`: immutable quad/batch contract.
- `nogc_sync_mut/text_layout/font_renderer.spl`: sole material owner.
- `compiler/70.backend/backend/gpu_portable_compute.spl`: portable artifact
  generation; Vulkan remains in its existing separate SPIR-V path.

### Public-to-next-layer surfaces

```simple
class FontRenderQuad
class FontRenderBatch
class FontGlyphRun

me FontRenderer.prepare_text(content: text, color: u32, font_size: i32) -> FontRenderBatch
me FontRenderer.prepare_glyph_run(run: FontGlyphRun, color: u32, font_size: i32) -> FontRenderBatch
fn emit_portable_font_atlas_composite_kernel(target: PortableComputeTarget) -> PortableComputeArtifact
me Engine3D.draw_text_hud(...)
me Engine3D.draw_text_world(...)
me Engine3D.draw_glyph_run_hud(...)
me Engine3D.draw_glyph_run_world(...)
```

`prepare_text` reuses the existing layout/glyph raster/cache path beside
`render_text_payload`; it does not perform a second whole-run payload pass.
Engine2D keeps `load_font` and `draw_text`; its implementation consumes the same
batch. No `GpuFontEmitter`, `SharedFontRenderer`, or second atlas cache is added.

## Visibility matrix

Each populated cell names the surface public to the parent node and to the next
consumer sibling. Everything else is tree-private.

| Raw layer | Catalog node | Material node | Artifact node |
|---|---|---|---|
| Pinned data | Parent: validated generated rows; next: immutable catalog lookup | — | — |
| Font registry | Parent: exact language/category policy cell; next: accepted asset binding | — | — |
| Renderer/shaper | — | Parent: `FontRenderBatch`; next: Engine2D/Engine3D batch consumption | — |
| Compiler emitter | — | — | Parent: paired optimization/font `PortableComputeArtifact` plans; next: toolchain/runtime adapters |
| Engine2D | — | Parent: existing `draw_text`; next: CUDA/Metal/OpenCL atlas adapters | Parent: conditional device readback; next: required verifier |
| Engine3D | — | Parent: `draw_text_hud`/`draw_text_world`; next: none | Parent: native texture/draw evidence; next: verifier |

## Target promotion flow

### WM/GUI/Web/2D resolved-font contract

`FontAssetCandidate` remains the only selected-asset identity authority. The
canonical `FontRenderer` owner adds `ResolvedFontMetrics` and
`resolve_font_metrics(family, text, size)`. A valid result contains the stable
manifest identity (`sha256=<hash>;axes=<defaults>`), exact ordered advances,
total width, and line height. It contains no native handle, glyph bitmap,
atlas, cache entry, or backend object.

Web semantic/layout resolves metrics before line wrapping. Its existing Draw IR
computed-style carrier may emit only `font-family`, `font-identity`, and
`font-advance-widths`. The Draw IR executor resolves the identity back through
the same registry, loads that exact face through `FontRenderer`, verifies the
prepared batch identity, then paints. Missing or mismatched identity fails back
to the unchanged bitmap route; paint-only selection is forbidden because it
would diverge from web wrapping. Legacy WM/GUI/manual Draw IR commands without
these keys remain byte- and pixel-compatible.

SimpleOS reuses the same `FontAssetCandidate`; it does not define another asset
record. The first guest face is pinned Noto Sans Mono at
`/assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`.
Release/QEMU disk, installer staging, initramfs, and legacy bake paths must stage
that exact length/hash through their existing payload contracts. Verified-byte
loading belongs in the current font facade and must precede WM startup; a guest
path marker without glyph/framebuffer evidence is not support.

The completion topology keeps all remaining paths on existing owners:

```text
Web semantic/layout ─┐
Widget/GUI scene ────┼─> DrawIrComposition ─> Engine2D.draw_text
WM scene ────────────┘                           │
                                                 └─> FontRenderer/FontRenderBatch

Engine3D.draw_text_{hud,world} ─────────────────────> same FontRenderer/FontRenderBatch
SimpleOS WM scene ─> DrawIrComposition ─> Engine2D ─> staged FontAssetCandidate
```

Legacy commands without `font-identity` retain bitmap text. Identified commands
must resolve the exact pinned candidate and live generation or clear vector
state before bitmap fallback. Unicode shaping fails closed until every run
vector and face binding agrees. Engine3D and SimpleOS evidence comes from their
own device/guest paths; host mirrors and test-only status fields are not valid
edges. Performance observation reuses existing renderer/backend counters and
timers rather than adding a benchmark-only renderer, cache, or upload path.

Current source includes provisional static catalog, CPU preparation, OpenCL
Engine2D atlas submission with image-blit fallback, Engine3D CPU compatibility,
and separate companion font artifacts in portable backend plans. The steps below remain the full
promotion contract, not current native-execution evidence.

1. Validate source hashes, font metadata, license, supported sfnt tables, and
   sparse language/category cells. Missing metadata is an error.
2. `FontRenderer.prepare_text` selects faces, shapes on CPU, rasterizes missing
   glyphs, updates only dirty atlas regions, and returns quads plus immutable
   atlas/cache identity.
3. The chosen engine creates or reuses a texture for that atlas generation and
   uploads dirty regions only. OpenCL performs row-offset writes after the
   initial full upload; allocation, invalidation, generation gaps, empty, or
   invalid dirty metadata fall back to a full upload.
4. A versioned emitted program samples alpha coverage and composes color. Source
   emission and compilation are recorded separately from execution.
5. Native promotion requires nonzero texture/sampler/pipeline handles, payload
   hash, draw/submit, completed fence, device-origin readback, an absolute
   nonblank glyph oracle, and CPU parity. Missing hardware is `unavailable`.
6. Device/compile/submit loss leaves the active CPU batch valid and falls back
   without changing its identity.

## Target cache and lifecycle

The existing `FontRenderer` cache must be extended in place. Target keys cover the selected
font checksum, face/default variation, glyph/run, render configuration,
transform/scale, backend/device features, emitted-program version, and dependency
generation. The owner reports hits, misses, evictions, bytes, generations, and
dirty regions. Engines cache only native resources keyed by the shared atlas
generation; they do not cache shaping or raster output independently.

## Rejected structures

- A second renderer/emitter/cache hierarchy: duplicates current owners.
- GPU shaping or outline rasterization: excluded and unnecessary for R1.
- A universal engine backend interface change: one promoted graphics route is
  sufficient; other routes stay compile/emission-only until proven.
- Direct runtime calls or environment-published fake payloads: bypass the
  existing facades and cannot prove native execution.

## Migration

1. Land deterministic manifests and fail-closed validation.
2. Add the two material values and `prepare_text`; harden shaping and cache keys.
3. Compile and inspect the planned portable atlas-composite companion artifacts.
4. Switch Engine2D internally while preserving its public API.
5. Add the two Engine3D entrypoints and promote one real graphics backend.
6. Update guides/SPipe recipes, then remove compatibility code only after parity
   and reference-removal gates pass.

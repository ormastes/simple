<!-- codex-research -->
# Shared Multilingual GPU Fonts — Local Research

Date: 2026-07-11

## Result

This is a consolidation and completion feature, not a greenfield font stack. The repository already contains most contracts, but they are split between the text-layout, Skia-like shaping, Engine2D, portable GPU emitter, game renderer, and Engine3D trees. No font binaries for the declared multilingual catalog are currently tracked at the paths used by `font_provider.spl`.

## Reusable paths

| Path | Current capability | Reuse/gap |
|---|---|---|
| `src/lib/common/encoding/font_registry.spl:1-359` | Catalog for ten named languages, six script groups, four categories, OFL labels and fallback | Reuse concept; ranking is stale/implicit, URLs are not immutable, and version/checksum/copyright/RFN/subset metadata is missing. |
| `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:42-359` | Canonical `FontRenderer`, bounded glyph cache, TTF/vector/bitmap selection, measurement and text payload | Extend rather than create `SharedFontRenderer`; cache key currently lacks face/config/backend dimensions. |
| `src/lib/nogc_sync_mut/text_layout/font_rasterizer.spl:47-720` | TTF/vector/bitmap rasterization, CPU oracle and payload-gated accelerator statistics | Existing environment-published glyph payload is an evidence bridge, not production GPU dispatch. |
| `src/lib/skia/feature/shaper/shaper.spl:1-633` | Pure Simple script segmentation, glyph runs, Arabic/Indic shaping skeleton and OpenType lookup use | Evaluate and harden before adding HarfBuzz; do not duplicate shaping. |
| `src/lib/skia/feature/text/bidi.spl:1-230` | Pure Simple UAX #9 subset | Reuse with conformance gaps made explicit. |
| `src/compiler/70.backend/backend/gpu_portable_compute.spl:241-271,503-758` | One logical kernel to CUDA, HIP, OpenCL, Metal and WebGPU source; compile/artifact contracts; bitmap glyph kernel | Required single emitter surface. Vulkan uses the separate generated SPIR-V contract. |
| `src/compiler/70.backend/backend/gpu_generated_2d_contract.spl:17-125` | Source, binary format, exported-symbol and artifact evidence | Reuse for font entries; emission/compile evidence remains below device execution. |
| `src/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl:15-100,266-369` | Request, artifact, submission and readback evidence stages | Reuse honesty ladder. |
| `src/lib/gc_async_mut/gpu/engine2d/engine.spl:638-702` | Public 2D font selection and one alpha-payload image blend | Existing 2D adapter target; shaping is not yet shared. |
| `src/lib/nogc_sync_mut/engine/render/font_atlas.spl:1-83` | ASCII atlas geometry only | Explicitly has no texture upload and renders tinted cells. |
| `src/lib/gc_async_mut/engine/render/gpu_pipeline.spl:201-220` | Game/3D-facing `DrawText` quad generation | Ignores real `FontId` resources and binds texture handle zero. |
| `src/lib/gc_async_mut/gpu/engine3d/backend.spl:82-159` | Texture, shader and compute API shape | Several concrete backends still emulate resource operations; native promotion needs per-backend proof. |
| `doc/09_report/simple_2d_vector_fonts_perf_2026-07-11.md` | Historical focused evidence | PENDING pure-Simple retained performance evidence; the recorded rows do not promote current native font execution. |

## Current backend truth

| Backend | Current text behavior | Claim allowed |
|---|---|---|
| Metal | Fixed 5x7 atlas is uploaded and submitted through a real MSL pipeline; device/mirror readback exists | Genuine bitmap-atlas composition for that fixed atlas only. |
| CUDA | CPU builds glyph/text pixels, then GPU performs nonzero/image copy; DtoH readback exists | GPU copy/composition, not GPU glyph rasterization. |
| HIP/ROCm | Generated source and runtime compile/lookup exist; text is CPU raster plus GPU blit | GPU blit only until a glyph kernel produces coverage. |
| Vulkan | Validated SPIR-V infrastructure exists; text is CPU raster/upload | No wired native glyph pipeline. |
| WebGPU | Portable WGSL source exists; 2D text/present reports CPU mirror | Source emission only. |
| 3D/game renderer | Atlas UV metadata and colored quads, no real atlas texture | No font rendering claim. |

## Existing duplication and stale documentation

- `common.text_layout.*` is already a compatibility facade over the canonical `nogc_sync_mut` implementation; a second shared library would be waste.
- `doc/05_design/lib/text_i18n/unicode_font_system.md` still labels TTF and complex shaping as future even though TTF rendering and a Pure Simple shaping skeleton now exist.
- `.claude/skills/spipe.md` correctly distinguishes emitter, compiled artifact, submit, readback and present; the new lane should generalize its fixed environment-payload font examples to the shared direct-dispatch path after selection.
- The prior `simple_2d_vector_fonts` requirement explicitly excluded shaping, atlas, 3D, and browser migration; this feature must extend it additively rather than silently rewriting its selected scope.

## Smallest coherent reuse direction

Keep `FontRenderer` as the shared CPU owner, adapt existing `SkGlyphRun`/`ShapedRun` output, reuse `PortableComputeArtifact`/compile/evidence types for font kernels, and make 2D plus 3D consumers accept the same immutable glyph-run/atlas resource. Preserve existing public entrypoints as deprecated adapters after parity. No source implementation or font asset import occurs before option selection.

## Sidecar review

- Local reuse was checked by the primary agent and the `font_local_reuse` sidecar.
- Backend emission/evidence was independently checked by `font_gpu_emission`; its conclusions match the source audit above.

## Current-state addendum — 2026-07-13

The tables above are the pre-selection baseline, not the current implementation.
The selected tree now bundles the pinned 16-file candidate catalog, exposes the
exact ten-language/ten-category sparse matrix, prepares one canonical
`FontRenderBatch`, and has CUDA, Metal, OpenCL, and Vulkan Engine2D adapters plus
an optional Vulkan Engine3D HUD/world adapter. Web semantic/layout, GUI, WM, and
SimpleOS converge through Draw IR and Engine2D. Native GPU, QEMU pixel, warm
performance, and canonical docgen evidence remain fail-closed and unpromoted.

## Current-state correction — 2026-07-14

The final sentence above was too broad. Web and widget/GUI composition producers
and the canonical SimpleOS desktop use the intended Draw IR/Engine2D ownership.
The hosted `HostCompositor.render_frame` still lowers its `SharedWmScene` through
the compatibility backend/pixel-buffer renderers. Canonical ARM64/x86_64
runner/readiness targets now select `gui_entry_desktop.spl`; direct legacy
`wm_entry.spl` files remain compatibility-only. The hosted frame owner remains
migration work. The latest retained SimpleOS fullscreen report also failed before
QEMU pixel acceptance, so source-complete canonical routing is runtime-unproven.

## Current-state correction — hosted WM and exact-corpus Emoji — 2026-07-14

The hosted color-background and top-level WM frame owner now executes
`SharedWmScene -> DrawIrComposition -> Engine2D` through one persistent
`Engine2dCompositorBackend`. Image/motion backgrounds and nested content retain
an immediate compatibility retry. This corrects the earlier hosted-owner note;
runtime pixel parity remains unproven.

The pinned monochrome `NotoEmoji[wght].ttf` exact `U+1F600` scenario also exits
0 under the self-hosted release binary for every selected language tag. REQ-005
defines acceptance by executable corpus coverage, so those ten exact tuples are
now native: the matrix is 67 native, 4 fallback, 26 not-designed, and 3
unavailable serif complex-script cells. This is not general Emoji support:
multi-codepoint, variation-selector, modifier, ZWJ, and color Emoji remain
fail-closed.

## Current-state serif probe addendum — 2026-07-14

Noto Serif Devanagari needs no second shaping path: the existing exact `dev2`
logic is face-structural, and an independent HarfBuzz oracle now pins glyphs,
clusters, and advances for `हिन्दी`. Noto Naskh Arabic needs one private profile
behind the existing `selected_arabic_glyphs` entrypoint; source now pins its
one-axis default, exact Arabic/Urdu lookup sequence, glyphs, advances, mark
offsets, RTL order, and malformed/wrong-language negatives. Both feed the same
canonical `FontRenderer` material gate.

The retained full pure-Simple CLI still embeds the tracked obsolete
`rt_env_set` ABI and then faults in another stale runtime boundary. Focused
font tests therefore exit 139 before assertions. The serif implementation and
oracles remain candidate readiness work; the 67/4/26/3 selection policy is
unchanged until a rebuilt current-ABI pure-Simple CLI executes them.

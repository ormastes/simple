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
| `src/lib/common/encoding/font_registry.spl` | Static pinned language/category catalog; nine identity-profile families, sans Devanagari/Arabic witness faces, and exact monochrome Noto Emoji `U+1F600` corpus coverage are accepted (12 total). Serif Devanagari/Arabic and two rank-eleven Bengali faces remain candidates. `selected_font_asset_for_language_category` resolves only accepted `native`/`fallback` cells to bundled candidates. |
| `src/app/release/install.spl` and `common/encoding/font_registry.spl` | Install the unchanged font/CLDR tree and notices below `share/simple`, then resolve selected registry-relative paths at the shared byte-load boundary through `SIMPLE_ASSET_ROOT`; hashes and exact installed-layout matching preserve one canonical candidate identity. |
| `src/lib/common/encoding/font_cldr_rank.spl` | Targeted, exact-arithmetic CLDR ranking core with fixture evidence. Pinned-source hashes and replay are source-complete; the deliberately narrow start-tag scanner is not a general XML validator, and fresh pure-Simple execution remains the gate. |
| `src/lib/common/encoding/sfnt.spl` | Neutral sfnt directory/fvar owner and typed default-`glyf` preflight shared by both production loaders; the old Skia parser modules are compatibility re-exports. |
| `src/lib/common/gpu/font_atlas_composite.spl` | Shared atlas subrect/color material plus exact HIP, OpenCL, Metal, and Vulkan GLSL sources used by compiler emission and runtime adapters. |
| `src/lib/nogc_sync_mut/text_layout/font_types.spl` | Canonical shared values; owns `FontGlyphRun`, `FontRenderQuad`, `FontRenderBatch`, `FontRenderConfig`, `FontExecutionPolicy`, and the pure execution-plan function. `FontGlyphRun` carries the exact revocable face handle/generation pair plus logical codepoint clusters; consumers validate liveness and never dereference the handle directly. |
| `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` | Canonical renderer, glyph cache, CPU payload; gains `prepare_text`, the bound glyph-run adapter, and fail-closed sfnt preflight before native loading. |
| `src/lib/common/ui/draw_ir.spl` and `draw_ir_sdn.spl` | Handle-free `DrawIrGlyphRunPayload` plus selected identity/ordered advances; shaped glyph IDs, positions, and logical clusters round-trip as semantic Draw IR while native faces, atlases, and caches remain executor-private. |
| `src/lib/skia/feature/shaper/shaper.spl` and `src/lib/skia/feature/text/bidi.spl` | Existing Pure Simple shaping/BiDi owners; exact per-fallback-face `OtFont` binding plus glyph/source/cluster/language/current-placement metadata are present. Source policy accepts the 54 no-feature identity cells, sans Hindi and Arabic/Urdu witnesses, four script-sans mono fallbacks, and the exact monochrome Noto Emoji `U+1F600` corpus tuple for all ten selected language tags. Exact default-instance Serif Devanagari and Naskh profiles plus independent oracle probes exist in source, but remain candidate-only until the pure-Simple runtime executes them. General GSUB/GPOS, marks, positioning, canonical language expansion, full BiDi, and Emoji sequences/color remain gated. |
| `src/compiler/70.backend/backend/gpu_portable_compute.spl` | Portable CUDA/HIP/OpenCL/Metal/WGSL artifacts; gains the atlas-composite emitter. |
| `src/app/portable_compute_emit/main.spl` | Stable pure-Simple CLI handoff to the existing portable/Vulkan emitters; emits source and identity markers only. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_cuda_font_ptx.spl` | Source-tracked CUDA font companion and independently compiled trust tuple; no renderer, cache, or discovery logic. |
| `src/compiler/70.backend/backend/gpu_generated_2d_contract.spl` | Version, symbol, compile-plan, and artifact evidence. |
| `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | Existing `load_font`/`draw_text` adapter; routes one canonical batch through CUDA, Metal, OpenCL, Vulkan, ROCm, then the CPU suffix fallback. |
| `src/lib/gc_async_mut/gpu/engine3d/engine.spl` | HUD/world facade and CPU fallback; an optional Vulkan adapter owns dedicated pipelines, R8 atlas upload, depth, fence, and device readback without changing the shared batch. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_{cuda,metal,opencl,vulkan,rocm}*.spl` | Backend-private upload/submission state keyed by the shared atlas owner and generation. Source wiring is not native promotion evidence. |
| `backend_vulkan_font_types.spl` plus `test/helpers/shared_multilingual_gpu_fonts_perf_evidence.spl` | Transient pipeline/composite stage observations stay with the Vulkan owner; ordered durable v5 serialization retains stage distributions and promotion facts without turning handles into reusable authority. |
| Web semantic/layout, GUI widget/scene, and shared WM scene producers | Preserve selected identity/advances in `DrawIrComposition`; Engine2D is the sole vector-material executor. Host Web uses the HTML/WebIR Draw IR owner; `ui.browser` executes one `widget_tree_to_draw_ir` composition and leaves queue dispatch neutral unless that composition is submitted. “WebIR” names the existing web semantic/layout layer, not a second drawing IR. Canonical SimpleOS and hosted color-background frames select the Draw IR/Engine2D route. Image/motion and nested hosted content retain compatibility fallback; direct legacy `wm_entry.spl` files are compatibility-only. |

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
   cache statistics, runtime font configuration/policy, and fallback.
   Rasterizer/shaper internals stay tree-private.
4. **Program artifacts:** the existing compiler portable-compute contract emits
   CUDA/HIP/OpenCL/Metal/WGSL font source and compile plans. Vulkan remains a
   separate pinned SPIR-V path for Engine2D atlas composition and Engine3D
   HUD/world rendering. No emitted or validated artifact may claim execution.
5. **Engine adapters:** Engine2D and Engine3D translate a `FontRenderBatch` into
   their own texture, sampler, transform, depth, submit, fence, and readback
   operations. Neither engine reads the other's private state.

### Common relative tree nodes

- `common/encoding/font_registry.spl`: validated catalog lookup.
- `nogc_sync_mut/text_layout/font_types.spl`: immutable config, policy,
  quad, and batch contract.
- `nogc_sync_mut/text_layout/font_renderer.spl`: sole material owner.
- `compiler/70.backend/backend/gpu_portable_compute.spl`: portable artifact
  generation; Vulkan remains in its existing separate SPIR-V path.

### Public-to-next-layer surfaces

```simple
class FontRenderQuad
class FontRenderBatch
class FontGlyphRun
class FontRenderConfig
enum FontExecutionPolicy
class DrawIrGlyphRunPayload

fn selected_font_asset_for_language_category(language: text, category: text) -> FontAssetCandidate?
me FontRenderer.prepare_text(content: text, color: u32, font_size: i32) -> FontRenderBatch
me FontRenderer.prepare_text_with_advances(content: text, advance_widths: [i32], color: u32, font_size: i32) -> FontRenderBatch
me FontRenderer.prepare_glyph_run(run: FontGlyphRun, color: u32, font_size: i32) -> FontRenderBatch
me FontRenderer.prepare_selected_glyph_run(payload: DrawIrGlyphRunPayload, color: u32, font_size: i32) -> FontRenderBatch
me FontRenderer.prepare_text_configured(content: text, color: u32, config: FontRenderConfig) -> FontRenderBatch
me FontRenderer.prepare_text_with_advances_configured(content: text, advance_widths: [i32], color: u32, config: FontRenderConfig) -> FontRenderBatch
me FontRenderer.prepare_glyph_run_configured(run: FontGlyphRun, color: u32, config: FontRenderConfig) -> FontRenderBatch
me FontRenderer.prepare_selected_glyph_run_configured(payload: DrawIrGlyphRunPayload, color: u32, config: FontRenderConfig) -> FontRenderBatch
me Engine2D.draw_text_configured(x: i32, y: i32, content: text, color: u32, config: FontRenderConfig) -> bool
me Engine2D.draw_text_with_advances_configured(x: i32, y: i32, content: text, advances: [i32], color: u32, config: FontRenderConfig) -> bool
me Engine2D.draw_shaped_text_configured(x: i32, y: i32, payload: DrawIrGlyphRunPayload, color: u32, config: FontRenderConfig) -> bool
fn emit_portable_font_atlas_composite_kernel(target: PortableComputeTarget) -> PortableComputeArtifact
me Engine3D.draw_text_hud(...)
me Engine3D.draw_text_world(...)
me Engine3D.draw_glyph_run_hud(...)
me Engine3D.draw_glyph_run_world(...)
me Engine3D.draw_text_hud_configured(...) -> bool
me Engine3D.draw_text_world_configured(...) -> bool
```

`prepare_text` reuses the existing layout/glyph raster/cache path beside
`render_text_payload`; it does not perform a second whole-run payload pass.
Engine2D keeps `load_font` and `draw_text`; its implementation consumes the same
batch. The Draw IR executor uses its internal `draw_text_with_advances` or
`draw_shaped_text` seam after exact identity validation; these are not new app
rendering paths. No `GpuFontEmitter`, `SharedFontRenderer`, or second atlas cache
is added.

The four configured methods are the REQ-015 public-to-next-layer surface.
Size-only methods construct `FontRenderConfig.default_for_size(font_size)` and
delegate. `FontRenderBatch` carries the length-delimited config identity,
execution target, and execution policy; the config object and all transient
material remain outside WebIR and Draw IR. Engine2D combines the existing
semantic IR fields with runtime-owned config. Its executable adapter order is
CUDA, Metal, OpenCL, Vulkan, ROCm, then CPU; Engine3D's is Vulkan then CPU.
`Suggested(auto)` uses that order. `Suggested(named)` tries the named target,
remaining executable GPU adapters in that order, then CPU. `Preferred(named)`
tries the named target then CPU; `Required(named)` tries only the named target
and returns failure. Concrete `cpu` is valid; `auto` with Preferred/Required and
unknown targets reject. Invalid modes
or CTM reject before any cache, counter, upload, or device mutation.
The shared `FontRenderBatch.material_supported()` root also rejects unknown
atlas-composite program versions and noncanonical transforms before either
engine adapter can mutate native state.
Non-default selection fields resolve through the canonical sparse matrix before
renderer mutation; the exact candidate identity is loaded or matched to a
caller-owned glyph run. Engine3D keeps one font target per frame and treats a
recorded Vulkan draw as pending until end-frame completion and exact readback.

## Visibility matrix

Each populated cell names the surface public to the parent node and to the next
consumer sibling. Everything else is tree-private.

| Raw layer | Catalog node | Material node | Artifact node |
|---|---|---|---|
| Pinned data | Parent: validated generated rows; next: immutable catalog lookup | — | — |
| Font registry | Parent: exact language/category policy cell; next: accepted asset binding | — | — |
| Renderer/shaper | — | Parent: `FontRenderConfig` + `FontRenderBatch`; next: Engine2D/Engine3D configured batch consumption | — |
| Compiler emitter | — | — | Parent: paired optimization/font `PortableComputeArtifact` plans; next: toolchain/runtime adapters |
| Engine2D | — | Parent: existing `draw_text`; next: CUDA/Metal/OpenCL/Vulkan/ROCm atlas adapters | Parent: conditional device readback; next: required verifier |
| Engine3D | — | Parent: `draw_text_hud`/`draw_text_world`; next: none | Parent: native texture/draw evidence; next: verifier |

## Target promotion flow

### WM/GUI/Web/2D resolved-font contract

`FontAssetCandidate` remains the only selected-asset identity authority. The
canonical `FontRenderer` owner adds `ResolvedFontMetrics` and
`resolve_font_metrics_with_language(family, text, size, language)`. A valid result contains the stable
manifest identity (`sha256=<hash>;axes=<defaults>`), exact ordered advances,
total width, line height, and—only for an accepted shaped run—a handle-free
`DrawIrGlyphRunPayload` of glyph IDs, positions, and logical clusters. It
contains no native handle, glyph bitmap, atlas, cache entry, or backend object.

Web semantic/layout resolves metrics before line wrapping. Its existing Draw IR
computed-style carrier emits `font-family`, `font-identity`, and ordered
`font-advance-widths`; an accepted shaped run also carries the semantic glyph
payload through SDN. The Draw IR executor resolves the identity back through
the same registry, loads that exact face through `FontRenderer`, verifies the
prepared batch identity, then paints. Missing, malformed, or mismatched
identity/payload fails back to the unchanged bitmap route; paint-only selection
is forbidden because it would diverge from web wrapping. Legacy WM/GUI/manual
Draw IR commands without these keys remain byte- and pixel-compatible.

SimpleOS reuses the same 16 `FontAssetCandidate` records; it does not define
another asset catalog. Image builders validate every canonical registry
identity, then store the exact bytes under readable registry-owned VFAT long
names in `/SYS/FONTS`; unique 8.3 aliases remain compatibility byte sources,
never alternate identities. The pure-Simple writer emits the LFN slots and the
shared pure-Simple reader resolves them before the raw 8.3 fallback.
This writer/reader contract is ASCII VFAT today: nested directories grow by FAT
cluster chains, while the fixed root cluster rejects more than 16 directory
slots instead of corrupting data. Non-ASCII UTF-16 LFN support remains pending.
The production Simple Browser registers those exact VFS bytes with the current
font facade before Web layout and Engine2D execution and rejects any skipped
Draw IR command. A guest path marker without glyph/framebuffer evidence is not
support.

Registered-only SimpleOS producers validate the pinned bytes and bind that
`OtFont` directly to the existing pure-Simple shaper with handle/generation
`0`; they never call the stubbed baremetal `rt_font_load_bytes`. The accepted
Arabic and Devanagari witnesses lower to handle-free `DrawIrGlyphRunPayload`,
then the existing registered `FontRasterizer` prepares `FontRenderBatch`
material. Hosted producers retain the live-face binding path. This source and
regression coverage is not retained QEMU framebuffer evidence.

The completion topology keeps all remaining paths on existing owners:

```text
Web semantic/layout ─┐
Widget/GUI scene ────┼─> DrawIrComposition ─> Engine2D.draw_text
SharedWmScene ───────┘                           │
                                                 └─> FontRenderer/FontRenderBatch

Engine3D.draw_text_{hud,world} ─────────────────────> same FontRenderer/FontRenderBatch
SimpleOS canonical desktop ─> Engine2dWmFrameExecutor ─> path above + staged FontAssetCandidate
Hosted HostCompositor ─> persistent Engine2dCompositorBackend ─> path above (color/top-level content)
Direct arch/*/wm_entry.spl invocation - - compatibility only; not a canonical target
```

Legacy commands without `font-identity` retain bitmap text. Identified commands
must resolve the exact pinned candidate and live generation or clear vector
state before bitmap fallback. The freestanding WM no-font-stack branch now
emits the canonical legacy bitmap text command; this is readable compatibility
fallback, not selected-font evidence. Unicode shaping fails closed until
every run vector and face binding agrees. Engine3D and SimpleOS evidence comes from their
own device/guest paths; host mirrors and test-only status fields are not valid
edges. Performance observation reuses existing renderer/backend counters and
timers rather than adding a benchmark-only renderer, cache, or upload path.

Current source includes the pinned catalog/matrix, canonical CPU preparation,
CUDA/Metal/OpenCL/Vulkan Engine2D atlas submission with suffix fallback, and an
optional Vulkan Engine3D HUD/world adapter. Web and widget/GUI producers lower
through Draw IR and Engine2D. Canonical SimpleOS ARM64/x86_64 runner/readiness
targets select `gui_entry_desktop.spl`, which lowers its `SharedWmScene` through
`Engine2dWmFrameExecutor`; direct legacy `wm_entry.spl` files remain
compatibility-only. Hosted color/top-level frames use a persistent
`Engine2dCompositorBackend` to execute `SharedWmScene -> DrawIrComposition ->
Engine2D`, with direct rendering retained for the programmatic compatibility
gate, image/motion backgrounds, nested content, or rejected readback. The
x86_64 SimpleOS entry registers the pinned face before composition and its `taskbar-clock` witness now
originates in `SharedWmScene -> DrawIrComposition -> Engine2D`. The old private
post-frame draw path is removed. The dynamic rightmost 56x48 QEMU crop is
source-wired. Retained evidence now binds and independently recomputes the
canonical wrapper, kernel ELF, and FAT32 image hashes; its expected pixel hash
and retained PASS remain pending.
Widget producers read existing `lang`/`font-family` properties, and
`SharedWmWindow.language` preserves explicit WM language; absent metadata stays
`und` and retains the previous Noto Sans Mono behavior.
No current pure-Simple full CLI is admitted. The earlier 208-symbol link wall
was resolved, but later retained rebuilds stopped at different Stage 4 parser,
LLVM construction, and resource-growth failures; none produced current
acceptance evidence. This is a compiler/runtime deployment defect, not
font-source failure, and neither a seed, minimal-stage binary, nor stale full
CLI is native acceptance evidence. Canonical `FontRenderer` fallback glyphs
are rasterized on CPU; environment-published accelerator pixels cannot enter `FontRenderBatch`
or its cache. GPU backends only compose the prepared alpha atlas.
The steps below remain the full promotion contract, not current native-execution
evidence.

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

The existing `FontRenderer` cache is extended in place. Current keys fence glyph
and resolved-metrics material with the live checksum/default-axis identity.
`FontRenderBatch` derives an atlas-owner identity from font identity, face
generation, numeric program version, the canonical rendering/transform
configuration identities, and dimensions; CUDA, OpenCL, Metal, ROCm, and
Vulkan combine that owner with dependency generation before reusing a
backend-local upload. Glyph-cache stats report hits, misses, evictions, bytes,
and generations; batches report dirty regions. Raster scale is the canonical
`font_size`, which is already part of glyph, atlas-entry, and resolved-metrics
keys. Translation is applied after atlas lookup and intentionally does not
invalidate atlas pixels. Rotation, skew, subpixel phase, and nonuniform scale
remain absent from the public renderer; distinct material identities no longer
alias, and the shared batch gate rejects unknown program versions and
noncanonical transforms. Complete target
keys must still add runtime program-artifact identity. Backend atlas resources
are bound to one immutable backend session: CUDA, OpenCL, and Vulkan reject
active reinitialization before retaining another session, and Metal releases
font state before device recreation. Thus an upload cache never crosses
device/context ownership. Engines do not cache shaping or raster output
independently.
CUDA font execution requires a verified generated PTX companion in a distinct
session module with an immutable PTX hash. The default CUDA 2D module contains
no font entry. If the companion is absent or rejected, CUDA font dispatch is
unavailable and Engine2D replays the batch from quad zero through its CPU
fallback policy.

ROCm compiles the exact shared `font_atlas_composite_hip_source` into its
existing HIP module, caches the versioned entry and atlas only inside that
backend, and returns the first unsubmitted quad so Engine2D can replay the
suffix on CPU. `hip` is a configuration alias for canonical target `rocm`.
This is source routing and fail-closed fallback coverage, not native AMD
submission or device-readback evidence.

Hosted native builds now link a separate optional `runtime_rocm.c` owner. It
loads HIP and HIPRTC at process scope without headers or link-time ROCm
dependencies, converts Simple arrays through runtime accessors, and exposes a
stable nonzero identity only when `hipDeviceGetUuid` succeeds. Engine2D clears
dirty state only after copy plus synchronization and labels a readback as
device-origin only with that UUID identity. A mock HIP/HIPRTC ABI checker covers
the provider and failure gates. The common GPU programs and portable codegen
use the same integer straight-ARGB rule as the CPU compositor: destination
weight includes destination alpha before RGB is divided by output alpha. The C
oracle fixes both transparent (`0x80c08040`) and translucent (`0xbf956030`)
results. `check-rocm-engine2d-font-readback.shs` then binds a configured-font
device readback to an admitted self-host binary, immutable source/binary hashes,
and retained runtime/device provenance; real AMD pixels remain the promotion
boundary.

Production deployment has a separate trust boundary from toolchain evidence.
Ignored `build/portable_compute_toolchains` output may prove emission and device
execution, but Engine2D never discovers it. The source-tracked
`backend_cuda_font_ptx.spl` owns the immutable PTX bytes, source/emitter hashes,
expected PTX SHA-256, entry, and common program version. Canonical CUDA
construction verifies the runtime PTX hash, entry, and program version before
attempting `install_cuda_font_artifact`. The checker and SPipe compare the
source/emitter hashes against a fresh Simple emission and fail closed on the
current recorded mismatch. A rejected companion
leaves primitive CUDA available while font dispatch follows the existing CPU
fallback policy. The current package verifier remains inadmissible because it
skips checksum validation and its builder emits a placeholder checksum.

Straight-ARGB correction increments a separate compositor semantics revision
without changing the version-1 entry ABI. The retained CUDA PTX and Vulkan
SPIR-V declare semantics revision 1; the common source declares revision 2.
Their runtime trust gates therefore reject the stale generated companions until
an admitted pure-Simple emitter regenerates source, artifacts, and pinned
identities. Dynamic source backends consume revision-2 source directly.

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
3. Compile and inspect the planned portable atlas-composite companion artifacts;
   native toolchain evidence must export the versioned font entry.
4. Switch Engine2D internally while preserving its public API.
5. Add the two Engine3D entrypoints and promote one real graphics backend.
6. Update guides/SPipe recipes, then remove compatibility code only after parity
   and reference-removal gates pass.

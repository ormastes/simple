# Shared Multilingual GPU Fonts

This guide separates the selected contract from what the current source proves.
The feature consolidates font selection and material preparation under the
existing `FontRenderer`; it does not introduce a second renderer.
Use `$sp_dev` as the process owner for bundled-font, shaping, glyph-material,
and GPU-text development lanes.

## Selected coverage

The reproducible CLDR 48.2 literate-functional ranking is:

`en`, `zh`, `es`, `hi`, `ar`, `fr`, `pt`, `ru`, `ur`, `id`

`bn` is retained as the eleventh-place boundary and useful extra candidate
coverage. The selected scripts are Latin, Simplified Han, Devanagari, Arabic,
and Cyrillic.

`common.encoding.font_cldr_rank` now provides the deterministic fixed-decimal
scanner, alias policy, per-script aggregation, and lexical tie break used by a
focused synthetic fixture. The exact CLDR 48.2
`common/supplemental/{supplementalData,supplementalMetadata,likelySubtags}.xml`
bytes, annotated-tag witness, source manifest, license, and derived top-eleven
ledger now live under `assets/fonts/cldr/release-48-2/`; their SHA-256 values
match the pinned upstream object. The real-input SPipe scenario regenerates the
ledger twice, independently recomputes all 1,589 contributions, and compares
every language total and script subtotal. This source is ready for that gate,
but no fresh Simple execution ran in this capped session, and the targeted
start-tag scanner remains non-validating XML.
The arithmetic fixture is
`test/01_unit/lib/common/encoding/font_cldr_rank_spec.spl`.

The ten product categories are sans, serif, mono, display, rounded,
handwriting, slab, blackletter, pixel, and emoji. This is a product taxonomy,
not a popularity ranking. Each language/category cell must say `native`,
`fallback`, `not-designed-for-script`, or `unavailable`; decorative Latin faces
must not be presented as native coverage for every language.
Here `native` means an accepted direct category face, not native GPU execution;
`fallback` means an explicit edge to another accepted face. Codepoint coverage
alone proves neither status.
Use `selected_font_coverage_cell(language, category)` for exact policy lookup;
unknown axes return `nil`. Do not load `witness_family` while the cell is
`unavailable` or `not-designed-for-script`.

Both native roots initialize exact selected bundled-font paths from their same
owned verified or prevalidated bytes. `spl_fonts` passes the pinned digest to
`rt_fonts_init_verified_bytes`; `font_sffi` hashes the selected blob in Simple
and calls `rt_font_load_bytes`. Equivalent aliases and other unmanaged fonts
retain legacy path loading and are outside the race-free claim. Neither path
promotes a coverage-matrix cell.

NFR: the current Pure Simple SHA helper converts `[u8]` to `[i64]`, temporarily
amplifying memory for candidates as large as 25 MiB. Replace or measure that
conversion before any runtime or coverage promotion.

## Pinned candidate assets

`selected_font_asset_candidates()` records 16 unchanged files from Google Fonts
commit `ec0464b978de222073645d6d3366f3fdf03376d8`, including script-specific Noto
Sans/Serif faces and these category witnesses: Noto Sans Mono, Bungee, Nunito,
Caveat, Roboto Slab, UnifrakturCook, Pixelify Sans, and monochrome Noto Emoji.
The catalog records paths, SHA-256, byte size, tables, scripts, license,
copyright, RFN state, upstream revision, embedded style/full/PostScript names,
embedded version, default variation axes, fallback role, and a hashed reference
to the canonical multilingual witness corpus.

The manifest scenario replays the pinned family, subfamily, full, PostScript,
and version strings from every real binary's sfnt `name` table. This is exact
asset identity evidence only; it neither enforces names during runtime loading
nor promotes language/category coverage.

The unchanged binaries and adjacent metadata/licenses are bundled under
`assets/fonts/google-fonts/` (16 files, 51,764,704 font bytes), but they remain
**acceptance candidates** where exact executable corpus coverage is pending.
The canonical font provider now projects all 16 manifest paths and accepts an
exact, trimmed, case-insensitive family name as a singleton candidate. Encoded
`@font-face` sources still take priority; generic CSS family heuristics remain
unchanged. Runtime addressability does not promote any sparse-matrix cell.
Do not call a face supported until shaping/codepoint tests and the sparse matrix
accept it. The selected policy permits only unchanged default variable-font
instances and requires non-default axes plus color/SVG/strike/CFF tables to
fail closed. Both native loader owners now call the Pure Simple structural
preflight before native state changes; it validates directory bounds/overlap,
required/excluded tables, and `fvar` defaults. The separate unrun manifest
scenario compares every exact table and default-axis record and retains typed
diagnostics. Loader bool/nil APIs do not surface those reasons. The incomplete
Pure Simple compound-outline parser and executable evidence remain open, so
REQ-008 is not yet complete.

A complete raw audit found 7,594 compound glyphs (16,194 components) in 14
candidate faces; the exact witness corpus reaches 76 roots and uses only
bounded XY-positioned components. The existing offset-only Pure Simple stub is
not a safe place to add that subset: its sibling simple decoder lacks glyph
slice bounds and original point identity. Native fontdue/stb rasterizers remain
the active compound owners until one glyph-ID/head+loca+maxp parser surface can
preserve points and reject malformed recursion.

The manifest scenario now prepares exact `CORPUS.sdn` codepoint and raster
witnesses for all 16 candidates, including Bengali rank 11 and Noto Emoji
`U+1F600`. This is evidence preparation only: the audit found no cell eligible
for promotion until a bound Pure Simple shaping acceptance run succeeds. The
matrix therefore remains 0 `native`, 0 `fallback`, 26
`not-designed-for-script`, and 74 `unavailable`. No Simple test ran in this
session because its three-attempt cap was already exhausted.

## Current shared material

The canonical implementation is
`std.nogc_sync_mut.text_layout.font_renderer.FontRenderer`, re-exported through
the other ownership variants. It now exposes:

```simple
val batch = renderer.prepare_text(content, color, font_size)
```

`FontRenderer` owns one bounded 1024×1024 shelf-packed white-alpha atlas.
`FontRenderBatch` carries stable per-glyph destination/atlas quads, codepoint and
byte-offset identity, color, atlas generation, the shared pixels, and only the
new dirty rectangles. Repeated warm glyphs keep coordinates/generation and
produce no dirty upload. Face changes or capacity overflow reset and repack the
atlas. Engine2D uses its established `load_font`/`draw_text` surface, and
Engine3D consumes the same batch through its CPU HUD/world compatibility path.
Its `draw_glyph_run_hud` and `draw_glyph_run_world` entrypoints reuse the same
neutral material, renderer, atlas, and stale-generation rejection. World
placement projects one anchor and draws a constant-pixel-size billboard; it is
not depth-tested native 3D text.

CPU code remains responsible for face selection, rasterization, fallback, and
cache identity. Complete Pure Simple complex-script shaping/BiDi is still a
tracked prerequisite; the built-in bitmap path remains the zero-config fallback.
Fontdue remains the basic layout/raster owner, while FreeType and stb provide
rasterization/metrics; none is shaping evidence. System HarfBuzz is not a
declared uniformly available dependency, and Rustybuzz is not added under
the selected Pure Simple contract.
The OpenType parser now supports validated Unicode cmap formats 4 and 12,
including bundled Noto Emoji `U+1F600`. Mixed-face fallback is not accepted yet
because complete per-script GSUB/GPOS and corpus evidence are still missing.
The shaper binds OpenType data by exact fallback face handle/generation; an
unbound or stale attached face never borrows another face's blob.

The opt-in shaped path now keeps each `ShapedGlyph`'s absolute source index,
cluster, current advance, and explicit zero offset through Arabic reversal,
provisional Devanagari reorder, and Thai mark clustering. `ShapedRun` adds
caller language identity (empty becomes `und`) while retaining script and
script-direction identity. Latin-1 letters no longer split Spanish, French, or
Portuguese witness runs, and mixed-script runs advance instead of overlapping.

Bind each OpenType blob to its runtime face with additive
`shaper_with_ot_face` calls; rebinding a handle replaces its prior snapshot. Only
Latin, Cyrillic, Han, and a single-codepoint emoji run may set
`glyph_indices_valid`, and only when the selected live face and blob/runtime
cmap glyph IDs agree. Arabic, Urdu, Devanagari, Bengali, Thai, Hebrew, and emoji
sequences fail closed. `substitution_complete` and `positioning_complete`
remain false because active-feature GSUB/GPOS and full BiDi are incomplete; current
advances/zero offsets are diagnostic placement, not shaping acceptance. Convert
substitution-complete direct runs with
`shaped_run_to_font_glyph_run`; incomplete runs remain non-renderable even when
their pre-GSUB glyph indices match. Engine2D consumes only that neutral text-layout
value through `draw_glyph_run`, preserving the batch-only layer boundary. It
carries a revocable generation token rather than a native face pointer. The
canonical renderer rejects mismatched or freed face handle/generation pairs and keys cache/atlas
entries by face + lifetime generation + glyph index + size. This is a bounded
renderer seam, not complete mixed-face GSUB/GPOS or automatic `draw_text`
shaping. The sparse matrix remains unchanged until executable corpus acceptance.

REQ-009 is partial: selected checksum/default-axis identity now fences the
whole glyph cache and atlas, stats expose that identity, and generation-bound
wrappers over the process-global face are revocable so stale operations fail
closed. Conditional real-dylib A-to-B evidence and its manual exist but remain
unexecuted under the session cap. This is not full rendering-config,
backend/device, or emitted-program keying, nor concurrent multi-face ownership;
it does not promote the coverage matrix.

## GPU code emission is not execution

Simple compiler code provides
`emit_portable_font_atlas_composite_kernel(target)`. It emits the versioned
`simple_font_atlas_composite_v1_u32` entry for CUDA, HIP, OpenCL, Metal, and
WGSL. `emit_vulkan_font_atlas_composite_source()` separately returns the
canonical Vulkan GLSL 450 source for GLSL-to-SPIR-V compilation; Vulkan is not
a `PortableComputeTarget`, and source emission is not compilation or execution.
The Vulkan shader's 15-input ABI is two storage-buffer bindings plus the exact
contiguous 13-field parameter block, and its entry is `main`.
`vulkan_font_atlas_compile_plan` records canonical source and external
GLSL-to-SPIR-V metadata; its evidence contract fails closed on missing bytes,
bad magic, or missing `main`. A valid synthetic contract is not compilation or
execution, and no compiled artifact exists absent real external capture.
Native-target signatures include explicit atlas/destination element counts and
guard computed indices; WGSL uses `arrayLength` for the same fail-closed bound.
Portable backend planning emits a separate optimization artifact and font
companion artifact for each selected target. The font path uses the
`_font_atlas` suffix and requires the versioned composite entry; it is not
concatenated with the optimization module (especially for WGSL, whose bindings
conflict). CUDA, native Metal, and OpenCL are the implemented runtime adapters.
CUDA appends a hand-written bounds-checked PTX companion to the existing single
2D module, uploads the atlas on generation change, marshals the exact 15-slot
pointer ABI, synchronizes each submitted quad, and mirrors only completed
prefixes. This PTX runtime provider is separate from compiler-emitted CUDA C.
Metal compiles the exact common MSL helper as an optional separate pipeline,
uses the fixed 13-word/52-byte parameter block, full-uploads changed atlas
generations, and dispatches completed 64-thread groups per quad. Only native
Metal receives the typed batch path; `metal-on-vulkan` remains excluded.
OpenCL `Engine2D.draw_text` uploads the shared atlas when its
generation changes. Its first/reset upload is full; consecutive generations
with valid dirty rectangles use checked per-row buffer offsets, while gaps or
invalid/empty metadata fail safe to a full upload. It then binds the exact
long-scalar ABI, submits one versioned
composite launch per quad, synchronizes, and falls back from the first
unsubmitted quad.

Every `FontRenderBatch` now stamps program version `1`, tied to
`simple_font_atlas_composite_v1_u32`. CUDA, native Metal, and OpenCL reject any
other version before atlas/session mutation; Engine2D then replays the CPU
fallback from quad 0. Conditional CUDA/OpenCL evidence covers mismatch
rejection followed by version-1 recovery. Metal currently has static rejection
evidence only because its session has no injectable dispatch seam. None of
this promotes native execution or completes REQ-009 program/backend cache
identity.

For OpenCL, compiler emission and Engine2D runtime compilation now share the
exact source returned by
`std.common.gpu.font_atlas_composite.font_atlas_composite_opencl_source()`.
The public call remains `Engine2D.draw_text`; direct session/backend launch is
an internal adapter. Font load/unload invalidates the cached atlas identity.
This source path is implemented but not promoted as native evidence until the
conditional device test runs and reports device-origin readback.

Do not add the entry name to metadata alone. Native CUDA/HIP uses a pointer-array
argument ABI, OpenCL needs explicit argument binding, Metal uses the packed
buffer-2 struct, and WGSL uses its own storage bindings. A backend becomes usable
only with matching upload, bind/launch, synchronization, and device readback.

An emitted source string or successful compile proves only emission/compilation.
Native promotion additionally requires nonzero texture/sampler/pipeline handles,
the submitted batch hash, draw/submit evidence, a completed fence,
device-origin readback, a nonblank absolute glyph oracle, and CPU comparison.
Missing hardware is `unavailable`, never a simulated pass.

Neutral shaped runs bind glyph IDs to the exact live face handle/generation and
preserve logical codepoint clusters. Those values are not UTF-8 byte offsets;
face liveness and every parallel vector length must match before rasterization.

## 2D and 3D status

- **2D:** `Engine2D.load_font` and `draw_text` are the supported public surface.
  CUDA, native Metal, and OpenCL attempt their shared versioned atlas-composite
  kernels first and retain per-glyph `draw_image_blend` for the unsubmitted
  suffix. Other backends retain image-blit compatibility. Source wiring alone
  is not device proof.
- **3D:** `load_font`, `draw_text_hud`, and `draw_text_world` consume the same
  batch through the CPU fallback; `draw_glyph_run_hud` and
  `draw_glyph_run_world` do the same for neutral runs, and world points use the
  stored camera matrices.
  The native blocker is a real texture upload/bind, sampler/pipeline,
  HUD/world transform and depth path, draw, fence, and device-origin readback on
  one graphics backend. Compute dispatch or CPU framebuffer output is not a
  substitute.

The repository also freezes an Engine3D-ready Metal HUD source/vertex contract.
It emits source and packed vertices only; no Engine3D method selects it and it
is not native execution evidence. A rejected runtime draft was removed because
interpreter readback was unsafe, atlas formats were ambiguous, GPU command
errors were ignored, child cleanup was unproven, and the macOS-only code could
not be compiled on this host. Web producers lower through web semantic/layout;
GUI producers lower through canonical widget/scene owners. Both emit Draw IR,
whose Engine2D executor may lower text to transient vector font batches. Do not
add a second font draw path or reuse Engine3D HUD/world as one.

## Evidence rules

Check structured batch/DrawIR/object state before pixels. Native evidence must
identify the actual backend and readback origin. Pixel equality, upload-only
records, emitted code, environment-published payloads, and CPU mirrors cannot
independently prove GPU execution.

See the [architecture](../../04_architecture/shared_multilingual_gpu_fonts.md),
[design](../../05_design/shared_multilingual_gpu_fonts.md), and
[requirements](../../02_requirements/feature/shared_multilingual_gpu_fonts.md).

<!-- codex-design -->
# Shared Multilingual GPU Fonts Detail Design

Status: selected design; manifest/assets, persistent atlas, portable emission,
Engine2D adapters, and optional Vulkan Engine3D source are implemented. Native
3D promotion remains open pending retained device evidence.

## Fixed interfaces

The implementation must use these names:

```simple
class FontRenderQuad
class FontRenderBatch
class FontRenderConfig
class FontGlyphRun
class DrawIrGlyphRunPayload

fn selected_font_asset_for_language_category(language: text, category: text) -> FontAssetCandidate?
me FontRenderer.prepare_text(content: text, color: u32, font_size: i32) -> FontRenderBatch
me FontRenderer.prepare_text_with_advances(content: text, advance_widths: [i32], color: u32, font_size: i32) -> FontRenderBatch
me FontRenderer.prepare_selected_glyph_run(payload: DrawIrGlyphRunPayload, color: u32, font_size: i32) -> FontRenderBatch
me FontRenderer.prepare_text_configured(content: text, color: u32, config: FontRenderConfig) -> FontRenderBatch
me FontRenderer.prepare_text_with_advances_configured(content: text, advance_widths: [i32], color: u32, config: FontRenderConfig) -> FontRenderBatch
me FontRenderer.prepare_glyph_run_configured(run: FontGlyphRun, color: u32, config: FontRenderConfig) -> FontRenderBatch
me FontRenderer.prepare_selected_glyph_run_configured(payload: DrawIrGlyphRunPayload, color: u32, config: FontRenderConfig) -> FontRenderBatch
fn emit_portable_font_atlas_composite_kernel(target: PortableComputeTarget) -> PortableComputeArtifact
me Engine2D.draw_text_configured(...)
me Engine2D.draw_text_with_advances_configured(...)
me Engine2D.draw_shaped_text_configured(...)
me Engine3D.draw_text_hud(...)
me Engine3D.draw_text_world(...)
me Engine3D.draw_glyph_run_hud(...)
me Engine3D.draw_glyph_run_world(...)
me Engine3D.draw_text_hud_configured(...)
me Engine3D.draw_text_world_configured(...)
```

The canonical values live in
`src/lib/nogc_sync_mut/text_layout/font_types.spl`; compatibility trees re-export
them. `FontRenderer.prepare_text` lives beside `render_text_payload` and reuses
the same lower-level layout/glyph raster/cache operations. The existing
Engine2D method names do not change.

## Data values

`FontRenderQuad` contains only what both engines need: glyph/cluster identity,
destination rectangle, atlas UV rectangle, color, and ordering. `FontRenderBatch`
contains quads, atlas dimensions/material, font/face checksum identity, atlas and
dependency generations, dirty rectangles, direction/script/language metadata,
and validity/fallback diagnostics. Values are immutable after preparation.
Preparation snapshots `font_identity` and `face_generation` even for empty or
invalid results. Glyph-run batches keep identity empty because the run supplies
only a revocable face generation, not a checksum identity.
The native rasterizer captures generation, identity, then generation again.
Stale capture returns `(0, "")`; a change observed during preparation discards
the transient material. This is coherence checking, not atomic global state.

The compatibility batch still exposes codepoint, byte offset, rectangles,
color, atlas generation/pixels, and dirty rectangles. The opt-in neutral
`FontGlyphRun` carries validated glyph positions, logical codepoint clusters,
and the exact revocable face handle/generation pair into the same renderer.
It does not claim UTF-8 byte clusters, language, full GSUB/GPOS, or complete
BiDi.

`DrawIrGlyphRunPayload` is the handle-free producer form: glyph IDs, x/y
positions, logical clusters, and validity only. It round-trips through Draw IR
SDN beside `font-identity` and ordered advances. The Engine2D executor first
resolves that identity to the live selected face, then calls
`prepare_selected_glyph_run`; unshaped selected text uses
`prepare_text_with_advances`. Neither form carries a face handle, atlas, cache,
or backend resource.
Positions are baseline pen offsets in device coordinates (+Y down). OpenType
GPOS y offsets are converted from +Y up at the shaper boundary. Rasterizers
store horizontal bitmap xmin and vertical bitmap bottom/ymin, so the shared
quad origin is `(pen_x + bearing_x, ascent + pen_y - bearing_y - height)` with
checked i32 bounds. Both shaped adapters use this formula; native bitmap x/y
offset accessors preserve the same contract for the legacy handle path.

`selected_font_coverage_cell(language, category)` is the fail-closed policy
lookup. Unknown axes return `nil`. A witness family is not loadable selection:
callers may bind an asset only after the returned status is `native` or
`fallback`. The policy binds 54 no-feature identity cells plus Noto Sans
Devanagari for exact Hindi `hi` and Noto Sans Arabic for the exact Arabic/Urdu
witnesses, plus exact monochrome Noto Emoji `U+1F600` corpus tuples for all ten
selected language tags: 67 native cells and 4 explicit script-sans mono
fallbacks. The other 29 cells are 26 `not-designed-for-script` and 3
`unavailable` serif complex-script cells.
The shaper now contains bounded, exact-default-instance Serif Devanagari and
Noto Naskh paths with independent HarfBuzz-pinned oracle probes. Selection does
not expose those three cells until the normal pure-Simple test CLI executes the
oracles and per-glyph canonical material checks successfully.
The resolver returns a bundled candidate only for those promoted cells. Widget
Draw IR reads the existing `lang` and `font-family` properties; shared WM
windows preserve an explicit language field. Missing language remains `und`
and keeps the previous monospace default, while an explicit language without a
family requests the multilingual sans fallback.

`ShapedGlyph` now owns absolute source/cluster identity and current advance/
offset values so reordering cannot detach metadata. `ShapedRun.language` is
caller metadata (`und` when omitted); script direction remains a per-run flag,
not UAX#9. Substitution and positioning completeness are true for the executed
no-feature Latin/Han/Cyrillic identity profile and the exact Hindi `hi`
witness. A bounded, table-derived Arabic/Urdu path covers only the two pinned
default-instance witnesses and is cataloged for those exact tuples. A whole-run
single `U+1F600` scalar has passed the self-hosted exact-face monochrome material
gate for every selected language tag and is cataloged only as that exact corpus
tuple. Other
complex-script, variation-selector, modifier, ZWJ, color, and multi-codepoint
emoji material remains incomplete even when blob/runtime cmap IDs match.

`Shaper` stores additive OpenType snapshots keyed by exact live face
handle/generation. Fallback resolves the snapshot after choosing its run font;
an attached face without an exact live binding never reuses the legacy unbound
parser blob.

GSUB decoding is staged: the parser owns table-bounded Coverage 1/2 and
SingleSubst 1/2 primitives, while the shaper stays identity until active
Script/LangSys/Feature lookup selection is available. Unsupported or malformed
data returns unchanged material and cannot set completion.

The selector and application land together. Accepted scope covers direct Latin,
Cyrillic, Han, and the exact Hindi `हिन्दी` witness. The Hindi path selects
`dev2` Script/LangSys records and only ordered
default feature tags; discretionary and inactive lookups cannot set completion.
Arabic/Urdu outside the two exact selected witnesses and other Indic sequences
remain fail-closed.

The bounded Arabic/Urdu path validates the selected Script/LangSys metadata,
then executes witness-specific pinned lookup indices/forms for exactly two
literals. The two passing HarfBuzz oracles promote only those exact tuples.
General feature selection, joining, mark attachment, contextual substitution,
positioning, and BiDi remain fail-closed.

The Metal source and 20-byte vertex contract remain emission-only. The optional
Vulkan Engine3D adapter owns dedicated HUD/world pipelines, R8 atlas upload,
depth test/write, zero-coverage discard, fenced submission, and device readback.
Neither source path is execution evidence: promotion still requires the retained
native oracle. Web producers lower through web semantic/layout (the current
WebIR), and GUI producers through canonical widget/scene owners; both emit Draw
IR. Engine2D alone lowers their text to transient `FontRenderBatch`; they must
not consume the Engine3D adapter as a parallel rendering path.

The revocable font-face handle/generation is intentionally present as opaque
rasterizer identity and is validated before use. Engine-owned texture, sampler,
pipeline, submission, fence, and readback handles stay out of both values; they
remain in the engine evidence record and are invalidated when the batch
generation changes.

## Deterministic language and asset manifests

The required language generator pins CLDR 48.2 source hashes. For each territory/language
row it applies fixed-decimal functional population and language literacy, using
territory literacy only when the language value is absent. It canonicalizes with
same-release aliases, does not roll up macrolanguages, aggregates by canonical
language, retains script totals, and sorts by descending total then lexical ID.
The manifest includes the eleventh row so the cutoff is executable evidence.

The required asset validator evaluates the selected 16-file catalog. A face is selectable
only when SHA-256, upstream revision, embedded names/version, copyright, SPDX
license, RFN/modification state, sfnt tables, file size, script/codepoint corpus,
category, and fallback role all match. Only unchanged `glyf` faces and default
variable-font instances pass. Unsupported tables or non-default axes return a
typed unsupported result before partial rendering.

The sparse matrix stores one of `native`, `fallback`,
`not-designed-for-script`, or `unavailable` for every language/category cell.
The renderer follows only declared fallback edges.

## Preparation algorithm

This is the target algorithm. Current compatibility material preparation covers
the atlas steps and both native loader owners now share the neutral default-glyf
preflight. The bounded compound corpus path, exact default-instance request
guard, and built-in monochrome bitmap fallback are implemented; broader legal
compound component modes, complete shaping, and complete cache keys remain open.

1. Resolve the requested family/category and the shaped run's language/script
   through the validated sparse matrix.
2. Use the existing Pure Simple BiDi/shaper flow to produce stable face, glyph,
   cluster, advance, offset, direction, language, and script identity.
3. Build the complete cache key before lookup. Reject unsupported format or
   variation requests without creating partial cache entries.
4. Rasterize cache misses on CPU using the existing rasterizer. The built-in
   monochrome bitmap path remains the zero-config fallback.
5. Pack new glyph coverage into the bounded shared atlas, record only changed
   rectangles, and increment generation once per committed atlas update.
6. Return one batch whose quad order is stable and whose atlas identity is the
   same for Engine2D and Engine3D.

Empty content returns a valid empty batch. Corrupt input returns an invalid batch
with a stable diagnostic and leaves the prior generation active.

## GPU artifact and execution

`emit_portable_font_atlas_composite_kernel` follows existing portable-compute
target syntax and returns a target, versioned entry name, source, and binary
format for CUDA, HIP, OpenCL, Metal, and WGSL. Each portable backend plan now
contains a separate optimization/font artifact pair with distinct paths; WGSL
is never concatenated because the modules own conflicting bindings. Exported-symbol and source/version-hash evidence
remain promotion gates rather than fields fabricated on the artifact.
The native toolchain checker preserves that pair as distinct PTX/HSACO/SPIR-V/
metallib files and rejects aggregate target readiness when either symbol set is
missing. It also compiles the canonical Vulkan GLSL into a separately validated
SPIR-V companion. Runtime promotion still requires loading the verified font
companion.
A bounded, embedded font-specific Vulkan SPIR-V contract is auto-installed by
the retained session. Its 10,772 bytes and SHA-256
`e25d25b8157fc2554822637603471a442f678eb58e20da167bfb023d7577880a` are pinned.
Only `precompiled-spirv` may become promotion-ready; runtime GLSL remains a
diagnostic API path. Conditional execution evidence remains environment-dependent.

Engine2D and Engine3D reuse the same common atlas subrect/color material.
Engine2D maps batch quads to the shared CUDA, native Metal, OpenCL, or Vulkan
atlas-composite launch when that backend is active. Each backend reuses its
upload only when the batch atlas-owner identity and atlas generation both
match, and invalidates on font replacement; an unsubmitted suffix uses the
image/alpha route. CUDA uses
the existing single PTX module and a 15-slot pointer ABI; OpenCL compiles the
shared source. CUDA's private runtime ABI is two pointer-valued `u64` slots plus
thirteen `s64` slots; it is intentionally distinct from compiler-emitted CUDA
C scalar widths, but its pointer array stores bounded values in 8-byte slots so
their low 32 bits satisfy the emitted `u32`/`i32` parameters. A generated PTX
companion may be installed into a distinct
session module keyed by its exact hash; font launches prefer it without
replacing the optimization module. The embedded PTX remains compatibility-only.
Other backends retain image/alpha compatibility. Engine3D
retains CPU HUD/world compatibility and now has dedicated Vulkan font pipeline,
sampler-descriptor, depth, fence, and device-readback ownership. Its atlas
texture is warm only when both canonical batch owner identity and dependency
generation match; replacement, failed upload, and shutdown invalidate that
authority. Promotion still waits for successful native pixel-oracle execution.
MetalSession compiles the exact common MSL as an optional separate library and
owns its pipeline. MetalBackend owns the persistent atlas owner + generation
pair and the 52-byte parameter policy, dispatching through the leak-free
completed-frame runtime call. The typed Metal lane is never set for
`metal-on-vulkan`.
After the first full OpenCL atlas upload, a consecutive generation with valid
dirty rectangles writes only the affected rows at checked byte offsets.
Allocation, invalidation, generation gaps, or invalid/empty dirty metadata use
the full-upload fail-safe. Engine3D now owns dedicated embedded-SPIR-V HUD and
depth-tested world font pipelines plus a combined sampler descriptor and device
readback adapter. Required native execution/readback promotion evidence remains
unproved.

The Vulkan promotion lane reports a compiled versioned entry,
nonzero handles, batch/payload hash, submit/draw, completed fence, device-origin
readback, accelerated device type, and backend/driver identity. Readback
authority requires the submitted command, its completed fence, the exact native
color-image handle and frame byte count, plus byte equality with the public
Engine3D result. A CPU mirror is a comparator, never the readback source.
Engine3D world depth is source-complete: the pipeline tests+writes depth,
zero-coverage fragments are discarded, and a translated-perspective four-frame
device oracle requires every fully opaque overlap pixel to retain the near
color in both draw orders. Native evidence resolves resources from logical
handles, never vector positions. A separate HUD-only oracle derives exact
nonzero pixel bounds and count from the canonical batch atlas and compares the
device readback at a fixed origin. Promotion remains open on native run
evidence.

## Resolved fonts across legacy UI, WebRender IR, Draw IR, and SimpleOS

The shared interface names are fixed:

- `ResolvedFontMetrics`
- `resolve_font_metrics(family, text, font_size)`
- Draw IR computed-style keys `font-family`, `font-identity`, and
  `font-advance-widths`

Resolution uses the existing provider/registry and `FontRenderer`; it does not
create a web renderer, atlas, or font cache. Web layout consumes exact ordered
advances for intrinsic width, wrapping, alignment, ellipsis, and line boxes.
Draw IR paint accepts a styled face only when its registry identity matches the
prepared `FontRenderBatch.font_identity`. Unstyled and failed resolution use the
old bitmap metrics and pixels unchanged. Mixed-family pages may reload the
process-global native face at command boundaries; a render-local last-identity
cache avoids redundant reloads. This serialized ceiling is deliberate; replace
it only when the native owner supports concurrent faces.

SimpleOS uses the existing selected candidate and verified-byte font facade.
The same Noto Sans Mono payload must be inserted by the release/QEMU disk C
builder, `ImageBuilder._populate_root_partition`, initramfs staging, and legacy
disk bake. The direct FAT32 builder exposes its 8.3 copy as
`/SYS/FONTS/NOTOSANS.TTF`; the guest retries that byte source under the
canonical registry identity, and both VFS implementations permit the pinned
1,708,408-byte payload within their 4 MiB read ceiling. Required guest evidence
is exact path/length/hash, successful glyph
material, WM Draw IR family/identity, and nonblank framebuffer output for Latin
plus one accepted non-ASCII simple-script witness. Host-repository presence is
not guest evidence.

Remaining completion behavior is intentionally narrow:

- Legacy Web, GUI, and WM text uses existing Draw IR scene helpers; paint code
  does not load fonts privately.
- Engine2D verifies a nonempty `font-identity` immediately before its existing
  `draw_text`. A missing identity uses the face already selected through the
  public Engine2D API (including SimpleOS retained-byte preload); an invalid or
  changed nonempty identity clears vector state and uses bitmap behavior.
- A selected-script run is accepted only when face generation, glyph IDs,
  clusters, advances, offsets, language, script, direction, and parallel vector
  lengths agree. Unsupported GSUB/GPOS lookups reject the run rather than
  returning a partial sequence.
- Engine3D HUD/world consumes `FontRenderBatch`; promotion requires real
  texture/sampler/pipeline/draw/fence/readback evidence from its chosen backend.
- SimpleOS validates the staged candidate/hash before boot and checks literal
  pixels produced by the guest WM. Pixelify uses a separate literal default-axis
  dimensions/advance/checksum format oracle.
- Performance uses warm cache/backend counters for 1,024 glyphs at 1080p/4K,
  4,096 equal-semantics CPU/GPU glyphs, unchanged uploads, RSS, and GPU
  resource high-water.

Evidence states are `pass`, `unavailable`, `runtime-blocked`, or a concrete
rejection. Helpers never translate the latter three into success.

## Runtime font configuration

`nogc_sync_mut.text_layout.font_types` owns one immutable `FontRenderConfig`;
UI, WebIR, Draw IR, Engine2D, and Engine3D must not define sibling font-policy
types. Its fields are family, category, language, script, size, weight, style,
hinting, antialiasing, atlas policy, execution target, and
`FontExecutionPolicy { Suggested, Preferred, Required }`. Registry categories
and backend targets remain validated text so the sync text-layout layer does
not depend on Skia or async compute types.

The default preserves today's rendering: `und`/`auto`, normal weight/style,
no hinting, grayscale antialiasing, the shared 1024 alpha atlas, target `auto`,
and `Suggested`. A length-delimited identity is part of glyph, shaped-run, and
atlas keys. Only that default rendering mode and uniform scale with late
translation are initially valid; rotation, skew, nonuniform/subpixel transform,
unsupported axes, and unsupported rendering modes reject before cache mutation.

Policy is observable. Engine2D supplies its executable font-adapter order
`cuda, metal, opencl, vulkan, cpu`; Engine3D supplies `vulkan, cpu`.
`Suggested(auto)` uses the supplied order, while `Suggested(named)` moves its
named target first and retains each remaining target once. `Preferred(named)`
tries the named target then CPU; `Required(named)` tries only the named target.
Concrete `cpu` is valid. Preferred/Required with `auto`, unknown targets, and
targets unsupported by that engine reject before mutation. Known-but-unavailable
targets follow the selected policy after recording the failure. Existing
size-only calls are default-config compatibility adapters. `FontRenderBatch`
carries config identity, target, and policy so configured bitmap,
selected-vector, shaped, Engine2D, and Engine3D paths share one contract.

## Failure and fallback

- Missing/corrupt manifest, license, hash, or unsupported sfnt data: reject face.
- Missing glyph: use only the declared fallback chain; otherwise report an
  unavailable cell and render the existing missing-glyph behavior.
- Compile, device, submit, fence, or device-loss failure: preserve the prepared
  batch and render through the CPU path when policy permits.
- `required` execution policy returns an error instead of silently falling back;
  `preferred` and `suggested` record the reason and use CPU.
- Any temporary SSpec helper calls `assert(false)` or `fail(...)`; no no-op pass.

## Observability and NFR measurement

Expose cache counters and stage timings for shaping, material preparation,
emission/compile, dirty upload, queue, device, synchronization, present/readback,
and CPU. Benchmark records include fixture hashes, viewport, color space,
premultiplication/rounding, warmups, samples, percentile method, host,
device/driver, RSS, and GPU resource high-water.

Promotion gates are the selected NFRs: at least 95% warm cache hits; 1,024 glyph
p95 no more than 4 ms at 1080p and 8 ms at 4K; equal-semantics 4,096 glyph p95 at
least 1.25x CPU; no unchanged full-atlas upload; at most 10% RSS growth, 128 MiB
GPU resources, and 80 MiB bundled core fonts/notices.

The performance SSpec is the sole collector. It overwrites
`build/shared_multilingual_gpu_fonts_perf/evidence.env`; the shared helper pins
the schema, fixture, font bytes, collector/helper and renderer/backend source
bundle hashes, device/driver, all counters, and four raw 11-sample arrays. The system promotion spec only
loads this record. Missing, stale, partial, malformed, or percentile-mismatched
records fail closed and never trigger a second measurement.

## Documentation impacts

Implementation updates the Unicode font, UI stack, Engine2D, Engine3D, GPU API,
backend-order, and pixel-comparison guides plus `THIRD_PARTY_NOTICES` and the
font-specific SPipe evidence recipe. Generic workflow skills change only where
the evidence semantics actually change.

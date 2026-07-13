<!-- codex-design -->
# Shared Multilingual GPU Fonts Detail Design

Status: selected design; manifest/assets, persistent atlas, portable emission,
and 2D/3D CPU compatibility are implemented. Native 3D promotion remains open.

## Fixed interfaces

The implementation must use these names:

```simple
class FontRenderQuad
class FontRenderBatch

me FontRenderer.prepare_text(content: text, color: u32, font_size: i32) -> FontRenderBatch
fn emit_portable_font_atlas_composite_kernel(target: PortableComputeTarget) -> PortableComputeArtifact
me Engine3D.draw_text_hud(...)
me Engine3D.draw_text_world(...)
me Engine3D.draw_glyph_run_hud(...)
me Engine3D.draw_glyph_run_world(...)
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

`selected_font_coverage_cell(language, category)` is the fail-closed policy
lookup. Unknown axes return `nil`. A witness family is not loadable selection:
callers may bind an asset only after the returned status is `native` or
`fallback`. Exact simple-script acceptance now binds 54 native cells and the
single `zh/mono -> Noto Sans SC` fallback; 45 cells remain unavailable or
not-designed.

`ShapedGlyph` now owns absolute source/cluster identity and current advance/
offset values so reordering cannot detach metadata. `ShapedRun.language` is
caller metadata (`und` when omitted); script direction remains a per-run flag,
not UAX#9. Substitution and positioning completeness are true only for the
executed no-feature Latin/Han/Cyrillic identity profile. Complex-script and
multi-codepoint emoji material remains incomplete and fails closed even when
blob/runtime cmap IDs match.

`Shaper` stores additive OpenType snapshots keyed by exact live face
handle/generation. Fallback resolves the snapshot after choosing its run font;
an attached face without an exact live binding never reuses the legacy unbound
parser blob.

GSUB decoding is staged: the parser owns table-bounded Coverage 1/2 and
SingleSubst 1/2 primitives, while the shaper stays identity until active
Script/LangSys/Feature lookup selection is available. Unsupported or malformed
data returns unchanged material and cannot set completion.

The selector and application land together. Accepted scope covers direct Latin,
Cyrillic, Han, bounded Arabic/Urdu letters, and the exact Hindi `हिन्दी`
witness. The Hindi path selects `dev2` Script/LangSys records and only ordered
default feature tags; discretionary and inactive lookups cannot set completion.
Other Indic sequences remain fail-closed.

The first native Engine3D HUD prerequisite is a Simple-owned Metal source and
20-byte vertex contract (`packed_float2` position, `packed_float2` UV, `u32`
color), with six vertices per validated atlas quad. The atlas format is frozen
to A8Unorm and render targets to RGBA8/BGRA8. This material is not execution:
native promotion still requires a compiled pipeline, texture upload, draw,
successful command completion, and device-origin texture readback. Web
producers lower through web semantic/layout and GUI producers through canonical
widget/scene owners; both emit Draw IR. The Engine2D executor may then lower
text to transient `FontRenderBatch`. They must not consume this Engine3D
adapter as a parallel rendering path.

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
A bounded font-specific Vulkan SPIR-V contract is installed by the retained
session. Conditional execution evidence remains environment-dependent.

Engine2D and Engine3D reuse the same common atlas subrect/color material.
Engine2D maps batch quads to the shared CUDA, native Metal, or OpenCL atlas-composite launch
when that backend is active, caching by atlas generation and invalidating on
font replacement; an unsubmitted suffix uses the image/alpha route. CUDA uses
the existing single PTX module and a 15-slot pointer ABI; OpenCL compiles the
shared source. CUDA's private runtime ABI is two pointer-valued `u64` slots plus
thirteen `s64` slots; it is intentionally distinct from compiler-emitted CUDA
C scalar widths. Other backends retain image/alpha compatibility. Engine3D
retains CPU HUD/world compatibility; its Vulkan owner now proves the untextured
mesh/depth/fence/readback prerequisite but cannot promote font textures until
the graphics pipeline owns a combined-image-sampler descriptor layout.
MetalSession compiles the exact common MSL as an optional separate library and
owns its pipeline. MetalBackend owns only persistent atlas generation and the
52-byte parameter policy, dispatching through the leak-free completed-frame
runtime call. The typed Metal lane is never set for `metal-on-vulkan`.
After the first full OpenCL atlas upload, a consecutive generation with valid
dirty rectangles writes only the affected rows at checked byte offsets.
Allocation, invalidation, generation gaps, or invalid/empty dirty metadata use
the full-upload fail-safe. Required native readback/promotion evidence remains
unproved.

The Vulkan promotion lane reports a compiled versioned entry,
nonzero handles, batch/payload hash, submit/draw, completed fence, device-origin
readback, accelerated device type, and backend/driver identity. A CPU mirror is
a comparator, never the readback source. Engine3D font promotion remains open.

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
disk bake. Required guest evidence is exact path/length/hash, successful glyph
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

## Documentation impacts

Implementation updates the Unicode font, UI stack, Engine2D, Engine3D, GPU API,
backend-order, and pixel-comparison guides plus `THIRD_PARTY_NOTICES` and the
font-specific SPipe evidence recipe. Generic workflow skills change only where
the evidence semantics actually change.

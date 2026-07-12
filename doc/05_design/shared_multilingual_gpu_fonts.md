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

The compatibility batch still exposes codepoint, byte offset, rectangles,
color, atlas generation/pixels, and dirty rectangles. The opt-in neutral
`FontGlyphRun` carries validated glyph positions, logical codepoint clusters,
and the exact revocable face handle/generation pair into the same renderer.
It does not claim UTF-8 byte clusters, language, full GSUB/GPOS, or complete
BiDi.

`selected_font_coverage_cell(language, category)` is the fail-closed policy
lookup. Unknown axes return `nil`. A witness family is not loadable selection:
callers may bind an asset only after the returned status is `native` or
`fallback`, which currently leaves every cell unbound.

`ShapedGlyph` now owns absolute source/cluster identity and current advance/
offset values so reordering cannot detach metadata. `ShapedRun.language` is
caller metadata (`und` when omitted); script direction remains a per-run flag,
not UAX#9. Both substitution and positioning completeness remain false.
Complex-script and multi-codepoint emoji material therefore fails closed even
when blob/runtime cmap IDs match.

`Shaper` stores additive OpenType snapshots keyed by exact live face
handle/generation. Fallback resolves the snapshot after choosing its run font;
an attached face without an exact live binding never reuses the legacy unbound
parser blob.

GSUB decoding is staged: the parser owns table-bounded Coverage 1/2 and
SingleSubst 1/2 primitives, while the shaper stays identity until active
Script/LangSys/Feature lookup selection is available. Unsupported or malformed
data returns unchanged material and cannot set completion.

The selector and application land together. Their first accepted scope covers
Latin, Cyrillic, Han, Devanagari, and Arabic script/language routing, with
table/parent-metadata bounds and a frozen per-script shaping-stage order.
Shared OpenType child offsets are legal and cannot be used as invented sibling
boundaries. Shared structural bytes may be memoized, but each reference validates
its own relative base and parent-metadata exclusion. Table addressing uses checked
wide arithmetic; an implementation storing absolute offsets in `u32` rejects a
GSUB end above `UINT32_MAX`. Common/Inherited marks resolve to the preceding strong
script, then following strong script, else unsupported; between different scripts
they attach to the preceding script. The exact initial stage arrays and required/
duplicate lookup rules are frozen as GSUB stage policy v1 in the shaping-gap
tracker. A valid selected SingleSubst that does not cover the current glyph is
a successful no-op, not an incomplete plan. A plan whose
`complete` bit is not derived from every validated
active subtable and whose final glyph IDs are not face-valid is rejected.

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
preflight. Complete shaping/cache keys and Pure Simple compound outlines remain
open.

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
A font-specific Vulkan SPIR-V contract remains required. Tests inspect source
syntax and entry markers, but never call that execution evidence.

Engine2D and Engine3D reuse the same common atlas subrect/color material.
Engine2D maps batch quads to the shared CUDA, native Metal, or OpenCL atlas-composite launch
when that backend is active, caching by atlas generation and invalidating on
font replacement; an unsubmitted suffix uses the image/alpha route. CUDA uses
the existing single PTX module and a 15-slot pointer ABI; OpenCL compiles the
shared source. CUDA's private runtime ABI is two pointer-valued `u64` slots plus
thirteen `s64` slots; it is intentionally distinct from compiler-emitted CUDA
C scalar widths. Other backends retain image/alpha compatibility. Engine3D
remains CPU HUD/world compatibility.
MetalSession compiles the exact common MSL as an optional separate library and
owns its pipeline. MetalBackend owns only persistent atlas generation and the
52-byte parameter policy, dispatching through the leak-free completed-frame
runtime call. The typed Metal lane is never set for `metal-on-vulkan`.
After the first full OpenCL atlas upload, a consecutive generation with valid
dirty rectangles writes only the affected rows at checked byte offsets.
Allocation, invalidation, generation gaps, or invalid/empty dirty metadata use
the full-upload fail-safe. Required native readback/promotion evidence remains
unproved.

The first promoted graphics backend must report compiled versioned entry,
nonzero handles, batch/payload hash, submit/draw, completed fence, device-origin
readback, and backend/driver identity. A CPU mirror is a comparator, never the
readback source.

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

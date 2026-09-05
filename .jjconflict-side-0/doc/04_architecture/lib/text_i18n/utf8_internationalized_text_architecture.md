<!-- codex-design -->

# UTF-8, Internationalized Text, and Rendering Architecture

## Decision

Simple retains one immutable validated-UTF-8 primitive, `text`. Unicode services, localization, layout, shaping, indexing, construction, and rendering are feature capsules layered above it. GUI/Web/WM semantic producers lower to `DrawIrComposition`; Engine2D alone lowers Draw IR text through `draw_text`. Engine3D HUD/world modes are sibling consumers of shared shaping and font material, never a shortcut around GUI/Web/Draw IR/Engine2D.

This document integrates, and does not replace, `doc/04_architecture/shared_multilingual_gpu_fonts.md`, `doc/04_architecture/simple_2d_vector_fonts.md`, and `doc/04_architecture/ui/simple_gui_stack.md`.

## Layered ownership

```text
Applications / compiler / editor / GUI / Web / Engine3D
  -> locale + message capsule       (LocaleContext, MessageIR)
  -> paragraph/layout capsule       (BiDi, segmentation, line layout, fallback)
  -> shaping capsule                (handle-free shaped runs and logical clusters)
  -> semantic 2D producer capsule   (DrawIrComposition / DrawIrGlyphRunPayload)
  -> rendering material capsule     (FontRenderer / transient FontRenderBatch)
  -> sibling consumers              (Engine2D adapters | Engine3D adapters)
  -> CPU/GPU backend-private resources

Bytes / streaming I/O
  -> TextDecoder / TextEncoder / TextSink
  -> validated UTF-8 text
  -> TextView / cursor / builder / optional indexed and grapheme views
```

### Public-to-next-layer rule

- byte owners publish validated `text`, progress, or typed errors;
- `text` publishes views, native boundary indexes, cursors, and explicit Unicode services;
- layout publishes logical runs, visual order, cluster maps, line metrics, and fallback face identity;
- shaping publishes glyph identity, offsets, advances, flags, and logical UTF-8 byte clusters;
- Draw IR publishes semantic text/style and optional handle-free shaped payload only;
- `FontRenderer` publishes a transient generation-bound `FontRenderBatch`;
- Engine2D/Engine3D adapters publish backend evidence, never renderer internals.

Sibling-private face handles, atlases, cache entries, buffers, pipelines, fences, textures, and readback state cannot cross upward or sideways.

## MDSOC application

The cross-cutting concerns are version/data provenance, capability selection, error policy, coverage, and performance observation. They are feature transforms over owners rather than fields embedded in every `text`:

- `UnicodeDataTransform` selects pinned property/table capabilities;
- `DecodePolicyTransform` selects strict/replacement/noalloc behavior;
- `TextEvidenceTransform` adds level-gated counters and typed receipts;
- `BackendSelectionTransform` selects scalar/SIMD or rendering backend without changing semantics;
- `LocaleBindingTransform` binds explicit request/task locale context;
- `AccessibilityTransform` retains semantic reading order, roles, bounds, and selection mapping beside pixels.

Locale, normalization, grapheme, display-width, renderer, and cache state must not be added to the base string header.

## Text and coordinate invariants

`text` is valid UTF-8, byte-exact for equality/hash, immutable, length-delimited, and allowed to contain U+0000. `TextIndex` is a proven native byte boundary. Scalar ordinal, grapheme ordinal, UTF-16 offset, display cell, glyph index, and visual position are distinct types or explicitly named operations.

Sequential movement uses `TextCursor`. Repeated scalar-ordinal access opts into owner-bound `IndexedText` with sparse checkpoints. Large editable documents use a provider/rope capsule with summarized byte/scalar/UTF-16/newline metrics; they do not change ordinary string layout.

## Decode and I/O boundary

Low-level `Read`/`Write` remain byte-oriented. `TextReader` and `TextWriter` compose transport with a stateful codec. Production decoding writes directly to a `TextSink`; an integer-code-point array is reference/test-only. Strict is default, unknown encodings fail, and every error reports absolute input offset, kind, offending prefix, and progress. Owned validated UTF-8 may be adopted; borrowed validated storage may produce a `TextSlice`.

## Layout and shaping boundary

Paragraph layout proceeds in logical order:

1. validate and preserve source byte spans;
2. segment paragraphs and resolve UAX #9 levels;
3. itemize direction/script/language/style/font fallback runs;
4. shape each run with logical byte clusters;
5. find UAX #14 opportunities and reshape at safe boundaries when required;
6. arrange visual runs and lines while retaining logical mappings;
7. expose grapheme-aware caret, selection, hit-test, and accessibility geometry.

The shaped-run cache key includes face and generation, variation axes, direction, script, language, feature set, fallback manifest, normalization/Unicode version, and shaper version. Incremental edits invalidate to safe-to-break/concat boundaries.

## Draw IR and Engine2D

`DrawIrGlyphRunPayload` is versioned and handle-free. It carries glyph IDs, x/y offsets, advances, logical byte clusters, and enough stable face/run identity to validate producer-resolved shaping without serializing a face handle. Missing, stale, malformed, or incompatible payloads fail closed; plain semantic text may still use the canonical consumer-resolved path.

Engine2D owns Draw IR execution. It resolves or validates shaping, calls `draw_text`/configured shaped variants, obtains transient `FontRenderBatch` material from the shared `FontRenderer`, and selects the backend. Web, GUI, WM, and platform presentation layers do not create a private glyph collector or font draw path.

## Engine3D sibling consumers

Engine3D reuses the same immutable shaped runs and `FontRenderer` material through adapter-private placement:

- HUD: viewport-space overlay with explicit DPI and depth-ignore policy;
- screen label: projected anchor with pixel sizing and optional depth test;
- spherical/cylindrical billboard: camera-facing world anchor with projected-size LOD;
- fixed world plane: full model transform, perspective, clipping, and depth policy;
- depth-aware annotation: world anchor, leader/layout constraints, visibility/occlusion behavior.

`Text3dPlacement` is Engine3D-only and contains transform/anchor/pivot, billboard mode, world or pixel scale, min/max projected pixels, depth test/write/bias, occlusion behavior, and clipping policy. It never enters Draw IR or `FontRenderBatch`.

The current projected-anchor implementation and separate font-only Vulkan target are compatibility prototypes. Completion requires one real scene color/depth render pass or an explicitly synchronized composite proving world occlusion and HUD overlay. CPU fallback must implement the same depth semantics or declare the mode unsupported before mutation.

Engine3D adapters use frame-owned ring/arena material and dirty-rectangle atlas updates. They must not allocate one native buffer per draw, upload a full atlas after one glyph, or return a font-only readback as scene-plus-text evidence.

## Raster representation policy

Bitmap/grayscale, hinted vector, SDF/MSDF/MTSDF, color bitmap/layer/paint, and path rendering are explicit policies selected by face capability, projected size, transform, target, and configuration. LCD/subpixel is rejected for unknown pixel geometry, rotated/perspective/transparent/3D/offscreen targets. LOD selection uses projected size with hysteresis. Cache keys include every visual identity dimension; rejected configs cannot mutate caches or backend state.

## Localization capsule

Localized syntax lowers to stable `MessageId`, typed `MessageSchema`, default `MessageIR`, and explicit `LocaleContext`. Catalog messages compile to one-pass sink instructions with CLDR plural/select and isolation. Static/default-only profiles dead-strip registry and data; mapped catalogs borrow validated blobs; embedded profiles use fixed sinks and bounded static tables.

## Evidence boundary

Semantic evidence precedes pixel evidence: decoded text → logical/visual runs → shaped clusters → transient batch → backend submission → fence/device completion → device-origin readback → CPU oracle parity. Source wiring, a synthetic batch, fallback bitmap, or screenshot cannot skip a rung.

Coverage uses a static owner branch manifest plus runtime hits so wholly unvisited decisions remain in the denominator. Every exclusion is reviewed and versioned. Performance receipts separate each pipeline stage and report latency, throughput, allocation, copied/transient bytes, RSS, atlas/VRAM, binary/data linkage, fallback, and exact backend identity.

## Rejected structures

- a second heap `Text`, default UTF-16/UTF-32, or implicit arbitrary-byte strings;
- hidden scalar/grapheme meaning for integer indexing;
- global character/locale mode as the core contract;
- process-global manual text-index handles;
- localization maps and repeated replacement on the hot path;
- private GUI/Web/Engine2D/Engine3D shapers, atlases, renderers, or dispatchers;
- persistent Draw IR atlas/UV/handle/device material;
- constant-depth screen quads described as full world text;
- performance PASS without memory evidence or 100% coverage from a denominator that omits unvisited branches.

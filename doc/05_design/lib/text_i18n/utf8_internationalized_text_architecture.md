<!-- codex-design -->

# UTF-8, Internationalized Text, and Rendering Detail Design

## Fixed interfaces

The fixed names are `TextView`, `TextSlice`, `TextIndex`, `TextCursor`, `TextBuilder`, `Utf8Buf<N>`, `TextDecoder`, `TextEncoder`, `TextSink`, `IndexedText`, `GraphemeView`, `LocaleContext`, `MessageId`, `MessageSchema`, `MessageIR`, `DrawIrComposition`, `DrawIrGlyphRunPayload`, `FontRenderConfig`, `FontRenderer`, and `FontRenderBatch`.

## Core data

```simple
struct DecodeProgress:
    input_read: i64
    output_written: i64
    status: DecodeStatus

trait TextDecoder:
    me decode_chunk(input: ByteSlice, output: TextSink, final: bool) -> DecodeProgress
    me reset()

struct ShapedTextRun:
    face_identity: text
    face_generation: i64
    direction: TextDirection
    script: ScriptId
    language: LanguageId
    glyph_ids: [i64]
    x_offsets: [f64]
    y_offsets: [f64]
    advances: [f64]
    byte_clusters: [i64]
    flags: [i64]

struct Text3dPlacement:
    mode: Text3dMode
    transform: Matrix4
    anchor_x: f64
    anchor_y: f64
    pivot_x: f64
    pivot_y: f64
    world_scale: f64
    min_pixel_size: f64
    max_pixel_size: f64
    depth_policy: TextDepthPolicy
    occlusion_policy: TextOcclusionPolicy
```

Final field representation follows existing Simple value-semantics constraints; arrays shown above are immutable logical data. GPU resources are absent.

## Algorithms

### Validated construction

Public byte construction validates once and returns `Result<text, Utf8Error>`. Lossy construction reports replacement count and first error. Only proof-producing validator/decoder/builder owners call the private trusted constructor. Boundary slicing validates both endpoints and returns `TextSlice` or `BoundaryError`.

### Streaming decode

Each decoder retains the minimum pending prefix/state. `decode_chunk` consumes as much input and sink capacity as possible, never emits malformed partial UTF-8, and returns `NeedInput`, `NeedOutput`, `Complete`, or typed `Error`. The scalar implementation defines maximal-subpart/replacement behavior; optimized kernels return identical progress.

### Cursor and indexing

`TextIndex.next` reads the lead byte and advances 1–4 bytes; `previous` scans backward over at most three continuations. `IndexedText` builds checkpoints lazily after measured repeated ordinal use; ASCII maps ordinal directly. The wrapper owns lifetime and invalidation.

### Paragraph layout and shaping

The layout owner resolves BiDi paragraph levels, script/language/style/fallback runs, then shapes logical runs. Cluster values are source byte offsets. Line breaking chooses legal opportunities and reshapes from a safe boundary when the shaper flags unsafe concatenation. Visual arrangement stores reversible logical maps for hit tests and selection.

### Draw IR serialization

`DrawIrGlyphRunPayload` validates equal array lengths, finite coordinates/advances, monotone logical clusters appropriate to direction, byte-boundary clusters inside source text, stable face identity, supported payload version, and glyph/count/byte bounds. SDN round-trip preserves every array exactly. It excludes atlas coordinates and resources.

### Shared material preparation

`FontRenderer.prepare_batch(run, config)` validates owner/generation/config, resolves representation, ensures glyphs in the shared atlas, records dirty rectangles, and returns immutable quad/material description plus generation identity. Engine2D and Engine3D adapters may consume the same prepared batch during its valid generation. Neither mutates it.

### Engine3D placement

HUD converts configured viewport/DPI positions directly. Screen labels project a world anchor and apply pixel-space layout. Billboards construct spherical or cylindrical camera-facing bases. Fixed-plane text transforms local glyph geometry through model/view/projection. Clipping happens before buffer emission; projected-size LOD uses hysteresis. World modes share the scene depth target; HUD ignores scene depth by policy. Coverage alpha controls color writes and, when enabled, depth writes.

### Frame material

Adapters accumulate glyph instances in a frame-owned arena/ring buffer, merge compatible draws by pipeline/atlas/config/depth policy, upload only dirty atlas rectangles, and retain resources until completion evidence. Device loss invalidates adapter resources but not logical shaped-run caches. Readback is separately timed and never included in queue-device time.

## Cache and invalidation table

| Cache | Key additions | Invalidated by |
|---|---|---|
| scalar checkpoints | text identity, stride | owner destruction/change |
| Unicode quick result | text identity, Unicode version, operation | version/text change |
| shape plan | face, script, language, direction, features, shaper version | face/shaper/config change |
| shaped run | text range, normalization, fallback manifest, plan key | edit to safe boundary, fallback/config/version change |
| raster glyph | face generation, glyph, size/LOD, axes, hint/AA, subpixel/transform class | face/config/device policy change |
| atlas slot | raster key, atlas generation | eviction/rebuild/device loss |
| message program | catalog hash/version, MessageId, schema | catalog/schema change |

## Failure ordering

Input, dimensions, finite values, payload shape, owner/generation, config compatibility, capacity, and backend availability are checked before cache insertion, telemetry mutation, upload, or submission. Partial streaming progress is explicit; rendering/material operations are transactional. Required policy never falls back; Preferred tries named target then CPU; Suggested follows canonical backend order then CPU.

## Migration waves

1. repair validation/boundary APIs and coverage denominator;
2. add views/cursors/builders/fixed sinks;
3. replace codec arrays with streaming direct output and split byte/text I/O;
4. refactor lexer to byte/block scanning and pinned identifiers;
5. add generated Unicode algorithms and conformance;
6. compile typed localization catalogs and explicit locale context;
7. version shaped Draw IR payload and close Web/GUI BiDi/fallback semantics;
8. converge Engine2D and Engine3D on shared batch consumption, dirty updates, and frame arenas;
9. implement complete Engine3D HUD/billboard/world/depth behavior and scene composition;
10. close forced-backend coverage/performance/device rows, then remove compatibility paths.

## Observability

Level-gated counters expose input bytes/scalars/graphemes, runs/glyphs, cache hits/misses, invalidated ranges, rasterized glyphs, atlas used/waste/dirty/upload bytes, batches/merged draws, vertex bytes, allocations/copied bytes, queue-device/fence/readback timings, fallback/rejection reason, and backend/config/manifest identity.

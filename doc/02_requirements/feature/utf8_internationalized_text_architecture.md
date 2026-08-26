<!-- codex-research -->

# UTF-8 and Internationalized Text Architecture Requirements

## Selection record

The user explicitly selected the full-scope lane on 2026-08-26: extend research, produce design and plans, include Simple 2D and 3D text rendering, and require intensive tests with 100% branch coverage and performance evidence across all supported rows. No narrower option is selected.

## Functional requirements

- REQ-001: `text` shall remain immutable, contiguous, and valid UTF-8; arbitrary bytes shall use byte types, and safe byte-to-text construction shall validate or explicitly replace malformed input.
- REQ-002: Public length, index, range, and conversion APIs shall identify byte, scalar, grapheme, UTF-16, or display-cell coordinates and document complexity.
- REQ-003: The text family shall provide `TextView`, `TextSlice`, `TextIndex`, `TextCursor`, `TextBuilder`, `Utf8Buf<N>`, `IndexedText`, and `GraphemeView` without introducing a competing base string object.
- REQ-004: UTF and supported legacy codecs shall decode incrementally and directly into `TextSink`, preserve state across chunks, and report typed absolute offsets and progress.
- REQ-005: Source parsing shall retain UTF-8 byte spans, use ASCII/block scanning with Unicode slow paths, borrow unchanged ranges, unify string scanners, and derive LSP/UI coordinates lazily.
- REQ-006: Unicode services shall use pinned generated Unicode 17.0.0 data for normalization, segmentation, identifier, case, BiDi, line-breaking, and security semantics, with declared tailoring.
- REQ-007: Localization shall use stable `MessageId`, typed `MessageSchema`, compiled one-pass `MessageIR`, explicit `LocaleContext`, CLDR 48.2.1 plural/select data, deterministic fallback, and substitution isolation.
- REQ-008: Default-only, single-locale, multi-locale, embedded/noalloc, and i18n-disabled profiles shall share semantics while linking only selected capabilities.
- REQ-009: GUI and Web producers shall emit semantic `DrawIrComposition`; shaped text may cross it only as handle-free `DrawIrGlyphRunPayload` containing glyph IDs, positions, advances, and logical clusters.
- REQ-010: Engine2D shall lower Draw IR text through `draw_text` and the canonical `FontRenderer`/transient `FontRenderBatch`; transient atlas, face, cache, and backend resources shall remain outside Draw IR.
- REQ-011: Engine3D HUD, screen-space, billboard, world-space, and depth-aware text shall be separate consumers of the same shaping, glyph, `FontRenderConfig`, `FontRenderer`, atlas, and batch ownership; Engine3D shall not bypass GUI/Web/Draw IR/Engine2D ownership.
- REQ-012: Text layout shall preserve logical-to-visual cluster mapping for cursor movement, selection, hit testing, accessibility, line breaking, BiDi, fallback, and diagnostics across 2D and 3D consumers.
- REQ-013: Rendering shall define DPI/scale, transforms, hinting, antialiasing, color-glyph, SDF/MSDF applicability, depth/occlusion, blending/color-space, fallback, and unsupported-mode behavior explicitly.
- REQ-014: Reference scalar, optimized portable, and SIMD/GPU paths shall implement one semantic contract and expose forced-backend differential evidence.
- REQ-015: Migration shall preserve initial `text` ABI and byte-oriented compatibility behavior while introducing explicit APIs and progressively rejecting ambiguous Unicode-sensitive use.
- REQ-016: The compiler AST extractor shall be the sole localization source of truth; independent line/regex scanners shall delegate or be removed.

## Traceability authority

The acceptance criteria and frozen test vocabulary live in `.spipe/utf8_internationalized_text_architecture/state.md`. The system-test plan maps every REQ above to executable evidence and records unavailable native rows as blocked rather than skipped.

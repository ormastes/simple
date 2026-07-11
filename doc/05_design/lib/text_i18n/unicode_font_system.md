# Unicode Font System — Design Document

**Date:** 2026-04-07
**Status:** Legacy Phase-1 baseline; superseded for font selection/rendering by
[`shared_multilingual_gpu_fonts.md`](../../shared_multilingual_gpu_fonts.md)
and the selected requirements in
`doc/02_requirements/feature/shared_multilingual_gpu_fonts.md`.

## Overview

Two-mode character encoding system with Unicode font support for 10 languages.

## Architecture

### Two Character Modes

| Mode | `len()` returns | Indexing | Default | Use case |
|------|-----------------|----------|---------|----------|
| `CharMode.Utf8` | byte count (O(1)) | byte offset (O(1)) | **YES** | Internal processing, I/O |
| `CharMode.FullUnicode` | codepoint count (O(n)) | codepoint index (O(n)) | no | User-facing text, UI |

### Module Layout

```
src/lib/common/
  encoding/
    mod.spl              — Module entry, re-exports all
    char_mode.spl        — CharMode enum, global mode setting
    utf8.spl             — UTF-8 encode/decode, validation
    utf16.spl            — UTF-16 encode/decode (LE/BE)
    utf32.spl            — UTF-32 encode/decode (LE/BE)
    codec.spl            — Encoding enum, encode/decode/transcode
    text_ops.spl         — Mode-aware ops (len, slice, chars, display width, script detection)
    unicode_text.spl     — Unicode-aware text functions (case, classify, trim, reverse)
    font_registry.spl    — Font catalog, fallback chain, script-to-font mapping
  unicode/
    mod.spl              — Module entry
    codepoint.spl        — Codepoint classification, case mapping, Hangul decomposition
```

### Encoding Codec System

```
Encoding enum: Utf8, Utf16LE, Utf16BE, Utf32LE, Utf32BE, Ascii, Latin1

encode(text, Encoding) -> [i64]     # text -> bytes
decode([i64], Encoding) -> text     # bytes -> text
transcode([i64], from, to) -> [i64] # bytes -> bytes (via codepoints)
```

### Legacy Font Organization

This table describes the old registry, not the selected top-ten oracle. It used
Korean to reach ten languages and covered only four font kinds. The replacement
derives `en, zh, es, hi, ar, fr, pt, ru, ur, id` from pinned CLDR 48.2 and uses a
ten-category sparse matrix. Indonesian is Latin-script; Urdu shares the Arabic
fallback; Bengali is rank 11 and remains extra coverage.

| # | Script Group | Languages | Sans | Serif | Mono | stb_truetype? |
|---|---|---|---|---|---|---|
| 1 | Latin+Cyrillic | EN, ES, FR, PT, RU | Noto Sans | Noto Serif | JetBrains Mono | YES |
| 2 | CJK-SC | Chinese | Noto Sans SC | Noto Serif SC | — | YES |
| 3 | Hangul | Korean (legacy, outside selected CLDR-derived set) | Noto Sans KR | Noto Serif KR | D2Coding | YES |
| 4 | Devanagari | Hindi | Noto Sans Devanagari | Noto Serif Devanagari | — | NO* |
| 5 | Arabic | Arabic | Noto Sans Arabic | Noto Naskh Arabic | — | NO* |
| 6 | Bengali | Bengali | Noto Sans Bengali | Noto Serif Bengali | — | NO* |

\* The selected implementation hardens the existing Pure Simple shaper/BiDi
path; this document's older HarfBuzz-only statement is no longer authoritative.

### OS Text Rendering (glass_render.c)

- Added UTF-8 decoder for text buffer processing
- `rt_gui_draw_text_vector()` now decodes UTF-8, handles wide chars
- `rt_gui_draw_text_buf()` now decodes UTF-8 sequences
- Non-ASCII renders as placeholder box with hex codepoint
- Font loading infrastructure (`rt_font_load_from_memory`)
- Glyph cache structure (LRU, 256 entries) for future TTF integration
- `cp_is_wide()` returns 2x advance for CJK/Hangul/fullwidth

### Tiered Implementation

- **Tier 1 (done):** UTF-8 decoding, encoding module, font registry, OS placeholder rendering
- **Current owner:** canonical `FontRenderer` with the existing `spl_fonts`
  TrueType path and bounded cache.
- **Selected extension:** shared `FontRenderBatch` material, portable Simple GPU
  atlas-composition emission, and common 2D/3D consumption.

## Key Decisions

1. **UTF-8 as default** — matches Rust internal representation, O(1) length
2. **Noto font family** — consistent design across all scripts, OFL licensed
3. **Fail closed** — missing/unsupported faces retain explicit fallback or
   unavailable state; no category/coverage claim is inferred from a filename.
4. **Pure Simple shaping selected** — complex-script conformance is executable
   work, not delegated to an undeclared HarfBuzz dependency.
5. **Pinned unchanged assets selected** — every imported binary requires exact
   upstream commit, checksum, license/RFN metadata, tables, size, and coverage.

# Simple 2D Vector Fonts — Feature Requirements

Date: 2026-07-11
Selection: Feature Option B

- REQ-001: Simple 2D loads a trusted local TTF/OTF through the existing font owner and reports failure without changing the active font.
- REQ-002: A loaded font renders deterministic nonblank antialiased glyphs through the public Simple 2D facade at two sizes.
- REQ-003: Measurement and rendering consistently apply advance, pair kerning, bearings, baseline/ascent, whitespace advance, and clipping.
- REQ-004: An owned fixture proves repeated glyphs and one directly mapped non-ASCII simple-script codepoint; missing glyphs retain bitmap fallback.
- REQ-005: Empty, missing, malformed, unsupported, and out-of-range input fails safely, inserts no partial cache entry, and leaves bitmap text usable.
- REQ-006: Identical `(font generation, glyph, size, raster mode)` requests hit cache; selecting another font invalidates prior-face entries.
- REQ-007: Bitmap `Engine2D.draw_text` remains the default until a vector font is explicitly selected.
- REQ-008: Reuse `FontRenderer`, the font I/O owner, and Engine2D readback; add no parser, shaping engine, atlas, raw feature-local runtime alias, or dependency.
- REQ-009: Repair the unresolved `rt_string_data` interpreter failure at the existing facade boundary with a focused regression.
- REQ-010: SSpec evidence uses the public facade and absolute layout/pixel/cache oracles; its manual shows load, render, warm-cache, and invalid-input flows.

Supported: trusted application/bundled TTF/OTF and simple-script Unicode mapping/kerning. Excluded: untrusted font parsing, WOFF/WOFF2, TTC selection, complex shaping/BiDi, SDF/MSDF, GPU atlas, and browser migration.

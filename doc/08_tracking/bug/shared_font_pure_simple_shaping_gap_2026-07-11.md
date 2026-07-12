# Pure-Simple shaping cannot feed the shared font renderer

Status: open — blocks shared multilingual GPU fonts REQ-005/007/009/012/013

## Problem

`FontRenderer` still prepares ordinary text as codepoints, while the existing
Skia shaper produces glyph IDs through an explicit neutral run. `FontGlyphRun`
now carries the exact live face handle/generation pair and logical codepoint
cluster positions, and the renderer rejects mismatches instead of reverse
resolving a generation globally. It still omits advances/offsets, direction,
language, script, and UTF-8 byte clusters. The current pure shaper is not an acceptance substitute:
its text conversion is ASCII-only, GSUB is identity, fallback retains one
global `OtFont`, and Arabic/Devanagari handling is
explicitly partial. Cyrillic and Urdu Arabic-extension script detection now
work, but detection alone does not provide accepted shaping.

Progress: the existing cmap owner now parses validated Unicode format 12 with
Windows 3/10 precedence, so bundled Noto Emoji resolves `U+1F600` to its real
glyph ID. Per-run face binding is still missing, so this does not promote emoji
fallback or mixed-face shaping.

## Smallest valid fix

1. Complete the existing `ShapedGlyph`/`FontGlyphRun` bridge while keeping the
   public `FontRenderBatch` seam stable.
2. Add an owned glyph-ID raster operation and key atlas entries by immutable
   face/default-variation identity + glyph ID + rendering configuration.
3. Reuse `text_codepoints`; complete decoded GSUB/GPOS, per-run faces,
   clusters, offsets, language/script/direction, and full selected-script
   behavior in the existing shaper.
4. Route prepared batches through that path and retain codepoint bitmap fallback.

## Acceptance

- Pinned Latin, Han, Devanagari, Arabic/Urdu, and Cyrillic fixtures expose stable
  face, glyph, cluster, advance, offsets, direction, language, and script.
- Rasterized glyph IDs match shaped output; missing glyphs/formats fail closed.
- The executable corpus gate promotes candidates only after every witness passes.

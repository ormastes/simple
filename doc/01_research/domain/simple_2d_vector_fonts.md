<!-- codex-research -->
# Simple 2D Vector Fonts — Domain Research

Date: 2026-07-11

- Scale once per `(face, pixel size)`; use ascent/descent/line gap and bitmap bearings around a baseline. See [FreeType glyph metrics](https://freetype.org/freetype2/docs/glyphs/glyphs-3.html).
- Basic stb pair kerning is adequate for simple scripts; [OpenType GPOS](https://learn.microsoft.com/en-us/typography/opentype/spec/gpos) is broader and confirms this is not complex shaping.
- Bound cache memory and key by face generation, glyph, size, raster flags, and subpixel phase when used. See the [FreeType cache subsystem](https://freetype.org/freetype2/docs/reference/ft2-cache_subsystem.html).
- Vendored [stb_truetype](https://github.com/nothings/stb/blob/master/stb_truetype.h) already supplies the required parser, metrics, glyph rasterization, and kerning, but warns against untrusted fonts because offsets are not fully range-checked.
- Benchmark font open, cold unique-glyph raster, warm repeated rendering, and mixed-size churn separately; record warmup, repetitions, p50/p95, cache counts, checksum, and RSS. See the [Google Benchmark guide](https://google.github.io/benchmark/user_guide.html).

Minimum path: trusted bundled TTF/OTF, correct metrics, bounded lazy glyph cache. Defer FreeType, shaping, SDF/MSDF, async eviction, and GPU atlases.

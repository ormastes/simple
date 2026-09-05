# Numeric HTML entities render as literal text in the web engine

- **Status:** Fixed (layout-renderer path, 2026-07-11)
- **Date:** 2026-07-11
- **Area:** lib / browser_engine (HTML entity decoding → text painting)
- **Severity:** P2 (visible garbage on any non-ASCII page)

## Symptom

Rendering live `https://www.google.com/` (Korean locale) through
`simple_web_layout_render_html_software_pixels` paints navigation link text as
the literal characters `&#51060;&#48120;&#51648;` instead of the decoded
"이미지". Named-entity handling exists (`src/lib/common/html/entities.spl`),
but numeric character references (`&#NNNNN;` / `&#xHHHH;`) are not decoded on
the path the layout renderer uses for text nodes.

## Repro

1. Save any HTML containing `&#51060;` in body text.
2. `PIXEL_HTML=<file> PIXEL_W=480 PIXEL_H=360 PIXEL_OUT_PPM=... PIXEL_OUT_JSON=... \
   bin/simple run tools/pixel_compare/render_and_save_simple.spl`
3. The literal `&#51060;` glyphs appear in the frame.

## Expected

Decode decimal and hex numeric character references to their code points
before text shaping, per WHATWG HTML tokenizer character-reference rules
(also needed: glyph coverage/fallback for non-Latin code points in the
bitmap rasterizer — track separately if the rasterizer lacks CJK glyphs;
an empty-box fallback is acceptable, literal `&#...;` text is not).

## Context

Found during the 2026-07-11 browser/web-engine hardening arc (live
google.com fetch through the now-runnable FetchEngine lane, commit
`f68e8def`).

## Fixed (2026-07-11, same day)

`_decode_numeric_entities` (decimal + hex, WHATWG-style, malformed refs kept
literal) now runs at the top of `decode_html_entities` in
`simple_web_html_layout_renderer.spl`, with `_codepoint_to_text` encoding
code points to UTF-8 through `rt_bytes_to_text` (the common-tier
`char_from_codepoint` returns U+FFFD for non-ASCII — separate latent gap,
left in place). Probe: decoded `&#66;/&#x44;/&#51060;…` renders
pixel-identical to the pre-decoded text and differs from the literal form.
Status: fixed on the layout-renderer path; the html_tokenizer path still has
no numeric decoding (follow-up if a consumer needs it).

# Default font-family: Chrome draws serif, Simple draws sans (2026-11-17)

**Status:** open. Found while re-pinning the 8 px text in `simple_web_renderer_spec`.

A page that sets no `font-family` is drawn by Chrome 159 in Liberation Serif
(`fc-match "Times New Roman"`), the `serif` default. The Simple web renderer draws the
same text in the sans face, so every default-family text run differs in glyph shape,
advance and x-height from Chrome before any hinting question arises.

## Evidence
Page: `simple_web_renderer_spec` "uses explicit line-height for wrapped text layout",
96x64, 8 px text, black on white variant.

- Chrome with no `font-family` renders byte-identically to Chrome with
  `font-family:serif` (screenshot compare).
- Simple with no `font-family` differs from Simple with `font-family:serif`.
- Whole-image mismatch against Chrome (any channel delta > 8):
  - same text, `font-family:sans-serif` on both sides: **318 px / 60,346 summed delta before
    the 8 px x-height fix, 106 px / 7,607 after**;
  - default family (Chrome serif vs Simple sans): 414 px / 61,454 before, 424 px / 76,493
    after. The fix makes the sans glyphs smaller while Chrome's serif glyphs stay as they
    were, so this page cannot judge glyph shape.

## Fix direction
Map the generic default (no `font-family`, and `serif`) to the Liberation Serif face the way
`sans-serif` maps to Liberation Sans; then re-measure the pins that assume sans text on
default-family pages (`simple_web_renderer_spec` 8 px darkest ink, currently `0xFF42375F`).

## Resolution (2026-11-18)
The default `Style.font_family` (style.spl, dom.spl) is now `serif`, as on Chrome 159 / Linux, where `getComputedStyle(body).fontFamily` is "Times New Roman" and fontconfig resolves it to Liberation Serif. The UA overrides survive: input/button/select stay on Liberation Sans, and code/kbd on DejaVu Sans Mono.

- **Pin:** `default_font_family_chrome159_spec` (3 cases). An unstyled span is 148 px wide; Chrome measures 147.69.
- **Measured effect** on the `simple_web_renderer_spec` 8 px wrapped-text page: the whole image against Chrome goes from 426 to **149** px, and the summed delta from 63,370 to **7,076**.
- **Gates:** the combo matrix and the 1x catalog are unchanged, because the catalog pages set their own fonts.

# Grey-glyph baseline one row high vs Chrome 159 (Liberation Sans 64px at 1x; several faces at dpr4), 2026-11-18

Status: open. Owner: the glyph raster anchoring lane (parked branch `work/webrender-gray-hint-20261117`).
Found by the dpr4 device-px line-metric lane. That lane fixes the line baseline. It does not fix where the painter puts the glyph relative to that baseline.

## Repro (1x, no device scale)

`<div style="font:64px 'Liberation Sans'">H<span style="display:inline-block;width:3px;height:1px;background:#00f"></span></div>`, body margin 0, 60x180, cpu_simd. Chrome 159.0.8154.6 headless, `--force-device-scale-factor=1`.

| | marker (baseline) rows | `H` ink rows |
|---|---|---|
| Chrome | 58 | 14-58 |
| Simple | 58 | 14-57 |

The box baseline matches: layout uses ascent round(57.94) = 58 and leading 2 → 1 above. The glyph ink ends one row early. Its top row matches and it is one row shorter.

DejaVu Sans 64px matches (ink ends at 132 on both).

## dpr4

The device-px line-metric lane measures each text run's glyph baseline against round(device ascent). The following still sit one row high against Chrome, after that lane, with the same signature:

- Liberation Sans 14/15/18/20px (56/60/72/80 device px);
- DejaVu Sans 20px (80 device px);
- Liberation Serif 13px (52 device px).

## Where to look

The painter's baseline comes from the native layout glyph `y` plus the glyph bitmap's bounding-box rounding (`font_renderer.spl` `prepare_text_with_advances`, `positioned.y`). It does not come from the SFNT hhea ascent that layout uses.

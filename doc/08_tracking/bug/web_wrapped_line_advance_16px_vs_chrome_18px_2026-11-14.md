# Wrapped text lines advance 16px where Chrome 159 advances 18px (2026-11-14)

**Status:** line advance FIXED 2026-11-14 (see "Fix"); one residual open ("Exact pixel value"). Originally: Found while fixing `font-family` list resolution; not part of that fix.

## Symptom

A block whose text wraps is too short, and every line after the first is painted too high.

Page (Chrome 159.0.8154.6, Linux, device scale 1):

```html
<div id="x" style="width:120px;font-family:FAMILY">Twitch commerce deterministic compatibility fixture</div>
```

| FAMILY | lines | Chrome `getBoundingClientRect().height` | Simple `simple_web_layout_debug_layout_by_id(..., "h")` |
|---|---|---|---|
| `sans-serif`, `Arial`, `"IBM Plex Sans", Arial, sans-serif` | 5 | 90 | 80 |
| `serif` | 4 | 72 | 64 |

Chrome advances 18px per line (`line-height: normal` of Liberation Sans / Liberation Serif at 16px); Simple advances 16px, the font size.
The first line agrees (ink rows 10-21 on both sides); the drift is 2px per following line.

Pixel evidence, 160x120 render of the corpus page used by
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
("paints famous-site corpus block geometry with Chrome default body margin"):
the fifth line ("fixture") has ink at rows 82-93 in Chrome and rows 74-85 in Simple, so pixel (32,93) is `0xFF000000` in Chrome and `0xFFFFFFFF` in Simple.

## Pinned by

`test/01_unit/browser_engine/wrapped_line_advance_normal_line_height_spec.spl` (line bands, block heights, per-size line heights).

The (32,93) probe used to sit in the block-geometry example of `simple_web_renderer_spec.spl`, pinned to white by `ff2dc6ed375` when the renderer painted no text at all. Chrome contradicts white, so it moved to the in-development spec with Chrome's value.

## Suspected cause (not verified)

`style_line_h` (`simple_web_html_layout_renderer_layout_foundation.spl`) returns `st.resolved_font_line_height` when it is positive. That value is `ResolvedFontMetrics.line_height`, which `font_renderer.spl` takes from `renderer.horizontal_line_metric(font_size, 3)` and replaces with `font_size` when the metric is `<= 0`. A 16px advance at 16px font size fits that fallback, i.e. the native line-metric entry answering 0, but the value was not printed. A single-line inline-block is 18px tall on both sides because that path uses `inline_content_area_height` (9/8 of the font size), not this metric.

## Not in scope here

Generic `monospace` blocks also differ (Chrome 60 = 4 lines x 15px at the UA 13px monospace size; Simple 80). That is the monospace default font size, a separate rule.

## Fix (2026-11-14)

Cause confirmed: a #text style took `ResolvedFontMetrics.line_height`, which is `font_size` whenever the foreign line metric answers 0 (it does on the pure-Simple outline lane), and an element style took `9 * (font_size / 8)`. Measured before the fix: text 12/16/24/32 and elements 9/18/27/36 at 12/16/24/32px.

One source now serves both: `browser_normal_line_height_px` (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`), called from `style_line_h`. It reads the face the family list resolves to and sums ascent, descent and line gap, each scaled and rounded on its own (`sfnt_blob_line_metric_units`, `src/lib/common/encoding/sfnt_kern.spl`).

| face | 12 | 16 | 24 | 32 |
|---|---|---|---|---|
| Liberation Sans (`sans-serif`) | 14 | 18 | 28 | 37 |
| Liberation Serif (`serif`) | 15 | 18 | 27 | 37 |
| DejaVu Sans Mono (`monospace`) | 14 | 19 | 28 | 38 |

Chrome 159 and Simple agree on all twelve. Element rows (`body{margin:0;font-family:sans-serif}`), Chrome / before / after:

| page | Chrome | before | after |
|---|---|---|---|
| `<div style="font-size:12px"><br>b</div>` | 28 | 21 | 28 |
| `<div style="font-size:24px"><br>b</div>` | 56 | 54 | 56 |
| `<div style="font-size:12px"><br><br></div>` | 28 | 18 | 28 |
| `<li>x</li>` at 12px / 24px | 14 / 28 | 12 / 27 | 14 / 28 |
| `<h1>x</h1>` | 37 | 36 | 37 |
| `<p style="width:60px">aa aa aa aa aa</p>` | 54 | 48 | 54 |
| `line-height:150%` at 16px / 24px | 24 / 36 | 2400 / 3600 | 24 / 36 |
| `<div style="line-height:2"><p style="line-height:normal">` | 18 | 32 | 18 |

Also fixed in the same function: a percentage parsed as a unitless factor (150% was 150x); `normal` parsed to "no value", so it could not replace an inherited factor; and a `font` shorthand did not reset line-height to normal (`<div style="line-height:2"><p style="font:16px sans-serif">` was 32, Chrome 18). Off the measured host `normal` keeps the element's previous value, so a form control stays on its UA line height.

**Metric source.** `OS/2` typo metrics when `fsSelection` bit 7 (USE_TYPO_METRICS) is set, else `hhea`. Chrome 159 honours the bit on this host: Pagul, Lohit Devanagari, Laksaman and Gargi all measure the typo prediction at 16/32/64px (Pagul 17/34/68 where `hhea` predicts 17/37/74).

**Scope.** Only the host the numbers were measured on (Liberation Sans/Serif/Mono present, no macOS system faces). Other hosts keep both previous values. `ResolvedFontMetrics.line_height` is not changed on any host, so non-web text (`common/ui/draw_ir.spl`, widget and window-scene text) is untouched. A TrueType collection has a `ttcf` header rather than an offset table; its metrics row is empty and the caller keeps the previous value.

**Why the gates did not move.** All three combo-matrix fixtures and all eight catalog pages declare `font: 16px/1.5 sans-serif`, so nothing in them uses `line-height: normal`. The same entry the matrix gate uses (`layout_geometry_diff.spl simple-geom`) reports the 60px three-line paragraph as `60x48` on the parent tree and `60x54` on the fixed one.

## Still open, found while measuring

- An empty `<li></li>` is 1px tall; Chrome gives it one line (14px at 12px, 28px at 24px sans-serif).
- `<code>` keeps the 16px inherited size (line 19px); Chrome applies the 13px monospace default (line 15px).
- `line-height` in `%` or `em` is kept as a factor and re-applied at a descendant's font size; CSS inherits the computed length. One decimal of precision (125% is 1.2x).

## Residual: exact pixel value

Pixel (32,93) is glyph ink on both sides now, but `0xFF000000` in Chrome and `0xFF808080` in Simple: edge coverage of the glyph rasterizer, not layout. Pinned by the in-development `test/01_unit/browser_engine/corpus_fifth_line_exact_pixel_spec.spl`.

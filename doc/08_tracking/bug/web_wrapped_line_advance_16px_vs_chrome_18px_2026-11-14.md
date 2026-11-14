# Wrapped text lines advance 16px where Chrome 159 advances 18px (2026-11-14)

**Status:** open. Found while fixing `font-family` list resolution; not part of that fix.

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

## What that spec does about it

The (32,93) probe was pinned to white by `ff2dc6ed375`, when the renderer painted no text at all. Chrome contradicts white, and black is red today, so the probe was removed from the example and this record filed. Restore it as `0xFF000000` when the advance is fixed.

## Suspected cause (not verified)

`style_line_h` (`simple_web_html_layout_renderer_layout_foundation.spl`) returns `st.resolved_font_line_height` when it is positive. That value is `ResolvedFontMetrics.line_height`, which `font_renderer.spl` takes from `renderer.horizontal_line_metric(font_size, 3)` and replaces with `font_size` when the metric is `<= 0`. A 16px advance at 16px font size fits that fallback, i.e. the native line-metric entry answering 0, but the value was not printed. A single-line inline-block is 18px tall on both sides because that path uses `inline_content_area_height` (9/8 of the font size), not this metric.

## Not in scope here

Generic `monospace` blocks also differ (Chrome 60 = 4 lines x 15px at the UA 13px monospace size; Simple 80). That is the monospace default font size, a separate rule.

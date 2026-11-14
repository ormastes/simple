# Web renderer: replaced-media residues against Chrome 159

**Status:** open. **Severity:** visual parity only; no crash, no blank output.
**Component:** `src/lib/gc_async_mut/gpu/browser_engine/` (layout + Draw IR paint).
**Oracle:** Chrome for Testing 159.0.8154.6, 900x760, `getBoundingClientRect`
and screenshot pixels.

The replaced-media change (`<canvas>`, `<svg>`, `<audio>`, `<video>` sized and
painted like Chrome 159) is pinned by:

- reproducing spec: `test/01_unit/browser_engine/replaced_media_geometry_spec.spl`
- generalization spec: `test/01_unit/browser_engine/replaced_media_paint_spec.spl`

Five differences from Chrome remain. None is asserted by those specs; each is
listed with its measurement and its unblock condition.

## 1. Inline `<svg>` paints `<rect>` only

`_html_draw_ir_svg_shape_commands`
(`simple_web_html_layout_renderer_paint_layout.spl`) lowers direct `<rect>`
children to Draw IR rects (x, y, width, height, fill, rx, viewBox, viewport
clip). `<circle>`, `<ellipse>`, `<line>`, `<polyline>`, `<polygon>`, `<path>`,
`<text>`, `<g>` nesting, `transform`, `stroke`, `opacity`, gradients and
`preserveAspectRatio` values other than the default are not painted.

The full SVG rasteriser `std.skia.feature.codec.svg_render`
(`decode_svg_to_argb_bounded`) exists but yields an image RESOURCE. The Draw IR
result (`SimpleWebLayoutDrawIrResult`) has no channel to return a resource, and
three of the four `_simple_web_layout_render_draw_ir_composition` call sites in
`simple_web_layout_engine2d_fast.spl` pass an empty image list.

Unblock: let the layout renderer return renderer-produced image resources with
the composition and thread them through every composition route; then
serialise the inline `<svg>` subtree and rasterise it with the skia decoder.

## 2. Media control icons and timelines are not drawn

`<audio controls>` paints only the `#f1f3f4` rounded pill; Chrome also draws a
play glyph, the `0:00 / 0:00` time text, a timeline track, a volume glyph and a
three-dot menu. `<video controls>` paints only the panel; Chrome draws the same
controls in white over it. The video panel's eased gradient is modelled as 16
flat bands on a linear ramp: `#333333` and `#000000` at the ends are exact, the
middle is within 8/255 (Chrome `#272727` at half height on a 120x150 box).

Unblock: a media-controls painter with Chrome's glyph geometry, and a gradient
Draw IR command for the scrim.

## 3. `<canvas width=120 height=40>` with border and padding is 120x40

Chrome 159: `<canvas width="120" height="40" style="border:2px solid
red;padding:3px">` under `box-sizing:border-box` is **130x50** -- the canvas
attributes are an intrinsic size, so padding and border are added around them.
`<svg width="120" height="40">` with the same style is **120x40** (svg
attributes are presentational CSS width/height). This renderer gives 120x40 for
both: `presentational_attr_decls`
(`simple_web_html_layout_renderer_core.spl:37`) maps `width`/`height` to CSS
for every tag, so the canvas attributes become a border-box size.

Unblock: stop mapping `width`/`height` to CSS for `<canvas>` and treat them as
the content size in `replaced_auto_box_w` / `replaced_auto_box_h`
(`simple_web_html_layout_renderer_layout_foundation.spl`).

## 4. Newline whitespace between inline siblings is dropped

`<span>x</span>\n<span>y</span>`: Chrome places the second span at x=12.45 (a
collapsed 4.45 px space); this renderer places it at x=8. The same holds
between replaced boxes, so on `examples/06_io/ui/web_catalog/animation.html`
the svg is at x=165 (Chrome 169.45), the audio at 285 (Chrome 293.9) and the
video at 585 (Chrome 593.9). A space written as a plain ` ` between siblings is
kept; only whitespace containing a newline is lost.

Unblock: keep a whitespace-only `#text` between two inline-level siblings as
one collapsible space regardless of which whitespace characters it contains.

## 5. Strut descent is 6 px where Chrome's is 7

A line holding a 150 px replaced box on the baseline is 157 px tall in Chrome
(16px/1.5 sans-serif: 150 + 7 px strut descent) and 156 px here
(`inline_line_baseline_descent`,
`simple_web_html_layout_renderer_layout_foundation.spl`). Every line made
taller than the line-height by an atomic inline is 1 px short, and the blocks
below sit 1 px high per such line.

Unblock: derive the strut ascent/descent from the resolved face metrics with
Chrome's rounding instead of `style_line_h - strut_baseline_offset`.

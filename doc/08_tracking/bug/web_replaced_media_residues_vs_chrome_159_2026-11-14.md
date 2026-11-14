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

## Follow-up 2026-11-14 (review of PR #9101)

Fixed and pinned by `test/01_unit/browser_engine/svg_viewbox_percent_sizing_spec.spl`
and `test/01_unit/browser_engine/svg_foreign_content_paint_spec.spl`: the
viewBox ratio on an auto axis, percentage width/height on svg/canvas/video,
`em` width/height, self-closing elements in svg/math foreign content,
`fill="currentColor"`, and a tab/newline-separated `viewBox`.

Paint gaps found in that review and still open (Chrome 159 pixels, same page
setup as above):

### 6. `<rect>` percentage attributes

`<svg width="40" height="40"><rect width="50%" height="50%" fill="#123456"/>`
paints a 20x20 rect in Chrome (percentages of the viewport, or of the viewBox
when there is one). `svg_number_milli` ignores the `%` suffix, so this renderer
paints 50x50 user units, clipped to the 40x40 viewport. The same applies to
`x`, `y`, `rx`, `ry`.

Unblock: resolve `%` on x/width/rx against the viewBox (or viewport) width and
on y/height/ry against its height in `_html_draw_ir_svg_shape_commands`.

### 7. `fill` from a CSS rule, and `fill="url(...)"`

`.g rect{fill:#00ffff}` with `<svg class="g"><rect width="20" height="20"/>`
is cyan in Chrome and black here: the painter reads `fill` from the shape's
`style` attribute and `fill` attribute only, because `Style` carries no `fill`
field for the cascade to fill in. `fill="url(#gradient)"` (paint servers) is
not supported either; `parse_color` returns 0 for it and nothing is painted,
where Chrome paints the gradient or pattern.

Unblock: a `fill` property in the cascade (`Style` field + `apply_decls`),
read by the painter after the presentation attribute; paint servers need the
gradient Draw IR command named in item 2.

### 8. Nested `<svg>`

`<svg width="40" height="40"><svg x="10" y="10" width="20" height="20"><rect
width="100" height="100" fill="#654321"/></svg></svg>` paints the rect in the
inner viewport only (Chrome: `#654321` at the centre, white at the outer
svg's corners). The painter walks DIRECT `<rect>` children of the outermost
svg, so the inner svg and its shapes are skipped and nothing is painted. `<g>`
grouping is skipped the same way (item 1).

Unblock: make the shape walk recursive with a viewport/transform stack, or
land the resource channel of item 1 and delegate to the skia rasteriser.

### 9. `em` lengths resolve against the font-size known when the declaration is applied

`width`/`height` in `em` now use `_decl_font_relative_length_px`, like
`min-width`/`max-width`. Measured (16 px page font, the other value 20 px):

| `height:2em` from | `font-size:20px` from | Chrome | Simple |
|---|---|---|---|
| stylesheet rule | inline `style` | 40 | **32** |
| inline `style` | stylesheet rule | 40 | 40 |
| rule `.c` | later rule `.b` | 40 | 40 |
| same rule, either order | same rule | 40 | 40 |

Only the first row differs: the rule's `em` is resolved before the inline
`font-size` is applied.

Unblock: store font-relative lengths unresolved and resolve them after the
cascade.

### 10. `foreignObject` and the foreign-content tag set

The tree builder honours a self-closing start tag when the nearest open
`svg`/`math` is reached before an open `foreignObject`. It does not implement
the HTML "breakout" list (`<svg><div>` closing the svg) or the MathML text
integration points.

### 11. viewBox-only `<svg>` in a shrink-to-fit container (mostly fixed)

Chrome 159 rule, measured (`viewBox="0 0 24 24"`, 900 px viewport): a
ratio-only svg contributes 0 to its container's min/max-content width, a
specified height contributes `height x ratio`, and the svg then fills the
width the container resolved to.

| case | Chrome | before (PR head `ee213029bb5`) | now |
|---|---|---|---|
| in `display:inline-block` | div 0, svg 0x0 | 300, 300x300 | 1, 1x1 |
| in `<button>` | 16, 0x0 | 316, 300x300 | 17, 1x1 |
| in `float:left` div | 0, 0x0 | 300, 300x300 | 1, 1x1 |
| in `position:absolute` div | 0, 0x0 | 1, 1x1 | 1, 1x1 |
| `height=48` in inline-block / float | 48, 48x48 | 300, 48x48 | 48, 48x48 |
| `height=48` in `<button>` | 64, 48x48 | 316, 48x48 | 64, 48x48 |
| inline-block with the text `hello` | 33.8, 33.8x33.8 | 334, 334x334 | 35, 35x35 |
| the svg itself `float:left` | 900x900 | 1x1 | 900x900 |
| the svg itself `position:absolute` in 500 px | 500x500 | 1x1 | 500x500 |
| inside `<span>a..b</span>` | 900x900 | not measured | 900x900 |
| block parent `width:400px` | 400x400 | 400x400 | 400x400 |
| flex row beside an 8 px span | 892x892 | 892x892 | 892x892 |

Owners: `inline_replaced_predicted_width`, `replaced_auto_box_w`,
`inline_box_holds_ratio_only_svg`, `absolute_outer_width`, and the float arm
of `layout_with_style`. Pinned by AC-12..AC-16 of
`test/01_unit/browser_engine/svg_viewbox_percent_sizing_spec.spl`.

Still open:

- **1 px box floor.** Every box width is floored at 1 px, so an EMPTY
  `display:inline-block` is 1x1 here and 0x0 in Chrome; the 0-wide rows above
  land on that floor (button 17 instead of 16); AC-12 asserts
  `<= Chrome + 1`, so it keeps passing when the floor goes. Unblock: let shrink-to-fit
  widths be 0 (about 25 `< 1` clamps in `layout_engine.spl`).
- **`display:inline-flex` is not a supported display keyword**: the box stays
  a full-width block (a text-only inline-flex is 900 wide here, 33.8 in
  Chrome), where Chrome shrinks it and a ratio-only svg is 0 wide. Base
  behaviour is retained there on purpose -- an unsized svg keeps the 300x150
  default instead of filling 900 px (`Style.display_inline_flex_authored`,
  set by the cascade in `core.spl`). 300x150 is not the Chrome value; AC-17
  asserts only `width <= 300`. Unblock: implement inline-flex as a
  shrink-to-fit flex container, then delete the flag.
- **Percentage width in a shrink-to-fit container**: `<svg viewBox
  style="width:50%">` in an inline-block is 150x150 in Chrome (the percentage
  falls back to the 300 px default for the container's intrinsic width) and
  1x1 here.

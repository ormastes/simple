# Static CPU lane faked pages without "text-document" tags (2026-10-05)

Status: FIXED (branch `work/browser-static-lane-real-layout`)

## Symptom

On the static CPU lane (`render_html_to_pixel_array` ->
`simple_web_engine2d_render_html_pixels`), a page with any background and a
plain `<div>` of text rendered a blank, background-colored frame. Found while
writing the gap-L spec: with a body background, its `<div class="t">` text
vanished. Whether a page was hit depended on incidental details; with the same
markup, class `t`, `a`, `b` or `s` came out blank, while `u`, `tt` or `x`
painted text.

## Root cause

`simple_web_engine2d_render_html_pixels` only ran real layout for a
"text document": a page whose source contains `<p`, `<h1-3`, `<button`,
`<span`, `<small`, `<code`, `<label` or `<a `. Every other page went
through a substring heuristic:

- `_html_background_color` and `_first_block_color` scanned the HTML text.
- The frame came back as one of three fakes:
  - a solid fill;
  - accent stripes every 17px, with a color keyed off `simple-web-success` /
    `simple-web-warning` class names;
  - a guessed 24x16 first-block rectangle, plus a "phantom" second block.
- No text was ever painted.

Whether a page escaped to real layout was decided by a selector
"resolvability" scan (`_style_block_has_class_or_id_selector`). This is a fake
output path, the same class as the 2026-07-14 gui/web dummy-implementation
audit.

## Fix

The heuristic is deleted:

- `SimpleWebHeuristicSurface`, `_solid_fill_pixels`, `_first_px_dimension`,
  `_html_accent_color`, the selector-resolvability scan, and the public
  routing seam `simple_web_html_needs_selector_layout` are all removed.
- Non-text documents now go through `simple_web_layout_render_html_pixels`,
  the real parse -> cascade -> layout -> paint engine that display:contents
  pages and unresolvable-selector pages already used.
- `simple_web_html_background_color` is kept. It is a scene-metadata helper
  used by `browser_renderer.spl` and `simple_web_renderer.spl`, not a pixel
  path.

## Specs

`test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl` pinned the routing
seam: three `it`s asserted which pages "stay on the fast path". They are
replaced by one that renders a page without text-document tags and asserts
two things: its div text is painted, and its `.card` block is laid out. The
"never paints an overridden class or id colour" case keeps its pixel
assertions; only its routing assert is removed.

Three more specs pinned the fake output. Each was re-derived from real
layout and checked on a PNG dump:

- `01_unit/.../simple_web_engine2d_renderer_spec` and its `test/unit`
  mirror, "keeps Simple Web marker off the solid-fill shortcut". This asserted
  the fabricated white 24x3 mark at (6,6). Real layout gives the navy body
  background with "Simple Web" painted in black, and no white pixels.
- `02_integration/rendering/web_engine2d_gpu_offload_parity_spec`, "Simple Web
  mark scene paints accent stripes". This asserted the fabricated
  `#2563EB` stripe column. Real layout gives a white body with the black
  text wrapped onto two lines at 80px, and no accent pixels.

Each of these new expectations fails against the old code: 72 fabricated
white pixels and 297 accent pixels.

## Perf of the formerly-faked pages

Measured with the interpreter, 400x300, mean of 5 renders, same seed and the
same base tree:

| page | fake (main) | real layout |
|---|---|---|
| bare text, no CSS | 181 ms | 549 ms |
| body bg + `<div class>` text | 148 ms | 484 ms |
| solid body color, empty body | 2 ms | 473 ms |
| two `.a` blocks | 145 ms | 469 ms |

Real layout costs about 0.47 s per frame here. That is the same pipeline every
"text document" page already paid. The fake was cheap because it did no work:
the empty-body solid fill was a single array fill. The cost is recorded here
rather than kept as a fake path.

Unblock for perf: the per-render fixed cost of the layout pipeline for
trivial documents (~0.47 s interpreted) belongs to the CSS/layout perf lane.

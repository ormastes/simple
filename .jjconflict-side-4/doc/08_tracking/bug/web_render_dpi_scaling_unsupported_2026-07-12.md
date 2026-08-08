# Web layout/paint engine has no device-pixel-ratio / DPI scaling hook

## Status

Open (feature gap, not a regression). Filed while wiring `SHOWCASE_DPI` into
`examples/06_io/ui/web_render_file_gui.spl` and
`web_standards_showcase_gui.spl` per the 4K/8K showcase resolution work.

## Context

The showcase resolution convention now supports `SHOWCASE_DPI` (default 300)
alongside `SHOWCASE_RESOLUTION` (default "4k" = 3840x2160). The intent is a
device-pixel-ratio style scale (300/96 ≈ 3.125) so text/borders/layout render
at 300-DPI density and stay crisp at 4K, not a 96-DPI page naively upscaled.

## Gap

`simple_web_render_html_to_pixels_with_engine2d_backend(html, width, height,
backend_name)` and the underlying
`simple_web_layout_render_html_software_pixels(html, width, height,
budget_ms)` (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`)
take a single `width`/`height` pair that serves **both** as the physical
raster buffer size (the pixel array returned) **and** as the CSS layout
viewport (used directly by `extract_css_vw` for `vw`/`vh` units and
`@media` queries, and by the box layout for percentage sizing). There is no
separate logical-viewport-vs-physical-raster-density parameter anywhere in
the parse → style → layout → paint pipeline — CSS `px` values map 1:1 to
output pixels.

Given that, there is no clean, scoped way to apply a device-pixel-ratio:
- Rendering at the full physical size (`3840x2160`) with `width` also driving
  the CSS viewport is what the code does today — this is DPI-neutral (1x),
  not "300 DPI-aware"; media queries/vw see the full 3840px viewport instead
  of a scaled-down logical one.
- Laying out at a smaller logical viewport (`3840/3.125 ≈ 1229px`) and then
  raster-scaling the resulting buffer up to 3840x2160 would be the naive
  upscale the DPI requirement explicitly rules out.
- A correct implementation needs a scale factor threaded through every unit
  conversion (px, em, rem, vw/vh, border-radius, font metrics, image/canvas
  sizing) in this ~9,500-line shared engine file, used by multiple other
  showcases (graphics/widget showcases, WM content-frame paint). That is a
  real engine feature addition, not a scoped perf/example fix, and carries
  real risk of regressing pixel-parity fixtures other agents own.

## Current behavior

`SHOWCASE_DPI` is read and reported in the showcase status line
(`dpi=<value> dpi_scale_applied=false`) but not applied. Output is rendered
at the requested physical resolution with no additional density scaling —
correct pixel count, but not "denser" text/borders than a 96-DPI render at
the same resolution would produce.

## Suggested follow-up

Thread an explicit `dpr: f64` (or `dpi: i32`) parameter through
`simple_web_render_html_to_pixels_with_engine2d_backend` →
`simple_web_engine2d_render_html_pixels` →
`simple_web_layout_render_html_software_pixels` → `layout`/`paint`, using it
to (a) divide the CSS viewport passed to `extract_css_vw`/layout by the DPR
for media-query/vw purposes while (b) multiplying resolved px lengths by the
DPR when computing box geometry and glyph metrics for the full-resolution
raster buffer. This is a genuine (if bounded) engine change and should be
scoped and reviewed on its own, not bundled into a showcase resolution bump.

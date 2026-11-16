# LCD text makes the Engine2D CPU text path about 44 % slower

Status: OPEN 2026-11-17, filed with `work/webrender-lcd-text-20261116`.

## Measurement

The page is 16 `<p>` lines of 11–13 px Liberation Sans, 480x280 CSS px. The backend is `cpu_simd` at 1x and `simple_web_render_html_to_pixels_at_device_scale` at k=4. Each figure is a warm run (glyph caches hot), the mean of 2–3 runs. The binary is the seed `/home/yoon/.cache/cargo-target-webrender-vk/release/simple` (59635056 B, 2026-11-14 09:32). Base and head ran back to back on the same host.

| lane | base | head | head, `SIMPLE_WEB_LCD_TEXT=0` | head, phases off |
|---|---|---|---|---|
| 1x warm | 3.28 s | 4.72 s (+44 %) | 3.29 s | 4.43 s |
| 4x warm | 28.5 s | 41.5 s (+46 %) | — | — |
| 1x cold | 14.8 s | 19.8 s | — | — |

`SIMPLE_WEB_LCD_TEXT=0` restores the base time. About 80 % of the cost is the composite and about 20 % is the quarter-phase pass.

## Cause

- **Composite (about 1.1 s at 1x).** `_draw_font_batch_cpu_suffix` takes one `read_pixels_region` per glyph quad. It then blends per channel in pure Simple (`engine2d_lcd_quad_composite`, three preblend lookups and three blends per pixel) and writes the quad back with `draw_image_blend`. The grayscale path makes a single blend call per quad.
- **Phase pass (about 0.3 s).** `_lcd_apply_pen_phases` reruns `_text_pen_milli` (advance and kerning lookups) for every staged run, every frame. `measure_text_advances` has already walked the same run.

## Fix plan

1. Composite in place on the CPU framebuffer for the whole batch. One frame borrow per batch, not a region copy per quad.
2. Return the milli pens from `measure_text_advances`, or memo them with its run memo, so the phase pass does not walk the run again.
3. Acceptance: the head 1x warm time is within 10 % of base on the page above, and `lcd_subpixel_text_chrome159_spec` stays 5/5.

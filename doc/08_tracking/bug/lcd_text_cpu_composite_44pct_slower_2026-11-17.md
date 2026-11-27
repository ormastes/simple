# LCD text makes the Engine2D CPU text path slower

Status: MITIGATED 2026-11-17. 1x is within the 10 % target; 4x is still +14 %. Filed with `work/webrender-lcd-text-20261116`.

## Measurement

- **Page.** 16 `<p>` lines of 11–13 px Liberation Sans, 480x280 CSS px. The backend is `cpu_simd` at 1x and `simple_web_render_html_to_pixels_at_device_scale` at k=4.
- **Runs.** Warm runs (glyph caches hot), mean of 2–3. Base, the first LCD commit and the optimised code ran back to back on the same host.
- **Binary.** The seed `/home/yoon/.cache/cargo-target-webrender-vk/release/simple` (59635056 B, 2026-11-14 09:32).

| lane | base | first LCD commit | optimised |
|---|---|---|---|
| 1x warm | 3.22 s | 4.66 s (+45 %) | 3.52 s (+9 %) |
| 4x warm | 26.6 s | 40.2 s (+51 %) | 30.4 s (+14 %) |

The output is unchanged by the optimisation. Whole-frame digests of the perf page and of a coloured-text page are identical between the first LCD commit and the optimised code, at 1x and 4x. The coloured page has white on indigo, amber on a gradient, translucent red, and 50 px grayscale text.

## What was fixed

- The LCD composite runs before the grayscale subrect, and the grayscale pixels are built only when LCD declines. Before this, every quad ran both loops.
- Coverage to Skia s32 tables, with the preblend and text alpha folded in, are cached per text colour. Before this, each pixel made three preblend lookups and three function calls.
- Zero-coverage cells copy `dst`. Full-coverage cells write the text colour. Row offsets are hoisted out of the pixel loop.
- The quarter-phase pass gets an O(1) atlas slot hint (`_lcd_phase_atlas_index`). Before this it scanned every atlas entry (`_font_atlas_entry_index`) for every phased glyph on every frame.

## What is left

- The per-pixel composite is still interpreted Simple. Mixed-coverage pixels do three table lookups and three blends each.
- Each quad still takes a `read_pixels_region` copy and a `draw_image_blend` pass.
- At 4x, the 11–12 px CSS text is 44–48 device px. It stays LCD, and its quads are 16x larger, so 4x pays proportionally more.
- Next step: a native span kernel for the LCD blend (like `rt_engine2d_simd_blend_span_u32`), taking per-channel coverage and the three s32 tables. It would blend in place on `SoftwareBackend.buf`, with no region copy.

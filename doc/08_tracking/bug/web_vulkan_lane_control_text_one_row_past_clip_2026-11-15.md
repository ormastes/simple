# Web renderer: the Vulkan lane paints some glyphs one row lower than the CPU lane

Status: OPEN. Found 2026-11-15 on `work/engine2d-lane-parity-20261115`
(base `fa2dd425635`), while listing every cpu_simd vs Vulkan (llvmpipe)
difference on the web catalog.

## Lane census (900x760, same seed, pixels with any channel off by more than 1)

Seed `$HOME/.cache/cargo-target-webrender-vk/release/simple` (59635056
bytes, 2026-11-14 09:32:20 +0900), `check-chrome-catalog-pixel-diff.shs`
`--backend cpu_simd` and `--backend vulkan` with
`VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json`; ppm-vs-ppm diff.

| page        | differing px | largest region                   | max |
|-------------|--------------|----------------------------------|-----|
| overview    | 2            | x480-495 y192-207                | 29  |
| html        | 2            | x128-143 y160-175                | 40  |
| css-layout  | 26           | x48-95 y368-383 (22 px, one row) | 125 |
| css-paint   | 0            |                                  |     |
| forms-media | 25           | x96-143 y144-159 (24 px)         | 232 |
| animation   | 1            | x240-255 y576-591                | 14  |
| evidence    | 0            |                                  |     |
| tab-bar     | 6            | three 1-4 px sites               | 131 |

62 pixels across 8 pages; the Chrome mismatch percentages are identical per
page in both lanes. Every site inspected is text ink: the Vulkan lane draws
a glyph row (or a descender) that the CPU lane does not. Chrome 159 agrees
with the CPU lane at the checked pixels (forms-media row 145 white,
css-layout (55,376) #64738a vs CPU #627289, Vulkan #172033).

The Engine2D primitives themselves agree: `feature_showcase.spl` (38
primitives, including `draw_gradient_rect_stops`) is byte-identical between
`VK2D_BACKEND=cpu` and `VK2D_BACKEND=vulkan` on llvmpipe (1,920,000 bytes).

## Repro (25 px)

`examples/06_io/ui/web_catalog/forms-media.html`'s `<style>` plus
`<label>Name <input value="Simple"></label><label>Choice <select><option>Alpha</option></select></label>`,
rendered 300x120 through `simple_web_render_html_to_pixels_with_engine2d_backend`
on `cpu_simd` and on `vulkan` (llvmpipe, interpreter): 25 differing pixels,
first at (60, 32). In the `<input>` value some glyph columns end at y 31 on
both lanes (x 67) while others (x 70, 74, 78) reach y 32 on Vulkan only: the
extra row is per glyph, not a uniform clip edge. Root cause not found.

## Where to look

`simple_web_layout_render_html_readback`
(`browser_engine/simple_web_html_engine2d_presenter.spl`) -> the text that
reaches `VulkanBackend` with a clip, and `vulkan_bitmap_text_clip_quads`
(`engine2d/backend_vulkan_font.spl:809`), whose own intersection is
exclusive on the right/bottom and looks correct, so the extra row more likely
comes from per-glyph height or `dst_y` derivation (`vulkan_bitmap_text_quads` /
`text_metrics`) versus the fb glyph blit; `browser_engine` sets no explicit
`set_clip`. Not fixed in this lane:
`browser_engine/**` was being edited by another lane on 2026-11-15.

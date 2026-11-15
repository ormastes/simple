# Web renderer: typing the `html` page's angled header gradient adds ~120 s to the catalog render

Status: FIXED 2026-11-15 (same lane). Found 2026-11-15 on `work/webrender-html-page-20261115`.

## Measurement

`examples/06_io/ui/web_render_page_ppm.spl`, page `html`, 900x760, backend
`cpu_simd`, seed `~/.cache/cargo-target-webrender-vk/release/simple`, one
process under `systemd-run --user --scope -p MemoryMax=8G`, host load 9-12:

| tree | wall |
|---|---|
| base (gradient painted flat as the first stop) | 212 s |
| + `background:` single-layer gradient typed (decl_apply only) | 334 s |
| + fb general raster (paint_primitives) | 330-337 s |
| + engine2d `emu_draw_linear_gradient_stops` stop-colour LUT | 329 s, ppm byte-identical |

So the cost is not the fb painter and not stop-colour evaluation. It appears
as soon as the header (`linear-gradient(120deg, #173b7a, #6d28d9)`, about
900x100) carries a typed gradient.

## Cause and fix

`emu_draw_linear_gradient_stops` (`src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl`)
run-merged equal colours into `draw_rect_filled` calls. At 120deg almost
every pixel differs from its neighbour, so the ~900x100 header became tens
of thousands of one-pixel `draw_rect_filled` calls. Stop-colour evaluation
was never the cost (the LUT row above). The fix builds each row and emits
ONE `draw_image` (or `draw_image_blend` when a stop has alpha) per row;
the trait already had both, so no new backend primitive was needed.

| tree | wall | ppm |
|---|---|---|
| tip before the fix | 329-337 s | reference |
| tip + per-row `draw_image` | 226 s (load 5.9) | byte-identical |

Same seed for both: `/home/yoon/.cache/cargo-target-webrender-vk/release/simple`,
59635056 bytes, mtime 2026-11-14 09:32:20 +0900. The remaining 14 s over
the 212 s base is the per-pixel ramp itself (the base painted one flat
rect), inside the run-to-run noise of this shared host.


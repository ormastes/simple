# Web renderer: typing the `html` page's angled header gradient adds ~120 s to the catalog render

Status: OPEN. Found 2026-11-15 on `work/webrender-html-page-20261115`.

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

## Suspect (not confirmed)

`emu_draw_linear_gradient_stops` (`src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl`)
run-merges equal colours into `draw_rect_filled` calls. At 120deg almost
every pixel differs from its neighbour, so the header becomes ~90,000
one-pixel `draw_rect_filled` calls through the Draw IR path. A per-row span
write (one call per scanline with a colour array) would remove that, but it
needs a new backend primitive across all engine2d backends.

## Not the fix

Painting the gradient flat again. The flat paint was 10.8 of the page's
15.98 mismatching points.

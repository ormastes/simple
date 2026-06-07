# Web Render Backend — pure_simple vs chromium

One interface, two interchangeable web-render engines, so the *same* HTML can be
rendered (and compared) by Simple's own renderer or by real Chromium.

- **API:** `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl`
- **Sample app:** `examples/06_io/ui/web_render_backend_gui.spl`
- **Chromium helper:** `tools/web-render-backend/chromium_render.js`

## The interface

```spl
use std.gc_async_mut.gpu.browser_engine.web_render_backend.{WebRenderBackend}

val r = WebRenderBackend.create("pure_simple", w, h)   # or "chromium"
val pixels = r.render_html_to_pixels(html)             # [u32] 0xAARRGGBB  (comparison)
val opened = r.show_live_window(html_path)             # true for chromium (live window)
```

| backend | display | nature |
|---------|---------|--------|
| `pure_simple` | software raster frame in a winit window | Simple's HTML layout → Engine2D `cpu_simd`. No browser. |
| `chromium` | **live, interactive** Electron `BrowserWindow` | real Chromium renders the live DOM. |

`render_html_to_pixels` produces a comparable buffer from **both** engines — this
is what the honest bit-level gate uses (pure-Simple ≡ Chromium OSR, `mismatch=0`).
`show_live_window` opens each backend's native window (chromium = live DOM;
pure_simple has no live shell and returns false so the caller presents pixels).

## Running the sample (macOS)

```bash
# pure-Simple raster window (software renderer)
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_render_backend_gui.spl pure_simple 384x288
# live Chromium window (real DOM, interactive) — viewport arg sets CSS width
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_render_backend_gui.spl chromium 1280x960
```

A `WxH` argv sets the CSS viewport (the page lays out at desktop width so fonts are
proportional); the result is downscaled to the window. A `.html` argv overrides the
page (default: `test/09_baselines/web_html_input/vanillastyle_demo.html`).

## Performance note (pure_simple)

The pure-Simple raster runs interpreted and is canvas-bound. Four O(n²)-class traps were
fixed (see `doc/08_tracking/bug/pure_simple_web_render_interpreter_bound_2026-06-06.md`):
1. heuristic-surface buffer built with a `push` loop → use `[0; w*h]` array-repeat;
2. the in-place array-write fix (`2d4579a0`) must be in the **running binary** —
   a stale `bin/simple` clones the framebuffer on every pixel write. Keep the
   driver current (rebuild on a stale deploy);
 3. per-node stylesheet rescans in `compute_styles()` reparsed `<style>` blocks
    and rematched selectors before the extracted rule loop applied the same CSS
    again. The 2026-06-07 fix applies extracted rules directly; a 40-rule /
    40-node 96x96 smoke improved `787368us -> 367032us` with unchanged checksum
   `39568413652567`;
4. recursive layout child discovery scanned the full flat node arena for each
   container. The 2026-06-07 child-link fix builds `first_child`/`next_sibling`
   arrays once; a 180-sibling 96x96 smoke improved `494990us -> 472511us` with
   unchanged checksum `39574588256768`.

The HTML layout Draw IR path now emits `text` commands for real text nodes with
font size, line height, glyph advance/scale, clip rect, parent id, and
`font-rendering=bitmap-vector-backend-preferred`. This gives native/GPU Draw IR
consumers a stable text contract before rasterization; the compatibility pixel
path still uses the pure-Simple 5x7 framebuffer rasterizer until a backend
consumes those text commands directly.
`engine2d_draw_ir_adv_*` now consumes the text contract by reading `font-size`,
rendering through FontRenderer-backed text blit buffers, and reporting
`font_offload_status`, `font_offload_reason`, `font_gpu_glyph_returned`, and
`font_production_ready` from the vector-font offload evidence helper. A status
such as `cpu-fallback` means routing and metadata are live while production GPU
dispatch is still missing; `gpu-glyph-returned` means the backend rasterizer
returned glyph pixels through the vector-font evidence path. The Draw IR text
executor also reports `font_text_cache_hits` / `font_text_cache_misses` for the
per-batch text-blit buffer cache; repeated identical labels should hit this
cache instead of re-running glyph layout and blit preparation.
Bitmap fallback follows the same evidence direction through
`rasterize_bitmap_accelerated()` and `bitmap_font_accelerator_stats()`: a
validated backend-returned bitmap glyph can bypass CPU mask generation and
record returned glyph/pixel counts. The production backend priority remains
host native first (`metal`, `cuda`, `hip`/ROCm, then `vulkan`/OpenCL by
availability) before CPU fallback; current bitmap/vector glyph tests prove the
return contract, not full live-kernel dispatch.

Keep pure_simple viewports modest (≤ ~400 wide); chromium opens a live window
and is unaffected.

## Honest comparison (no memorized pixels)

Use two **independently produced** artifacts + an absolute oracle, never hard-coded
captured pixels. Gate: `scripts/check/check-electron-simple-web-engine2d-bitmap-evidence.shs`
(pure-Simple Engine2D vs real Chromium OSR → `mismatch_count=0`).

See also: [`web_render_backend_tldr.md`](web_render_backend_tldr.md).

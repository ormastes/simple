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
| `pure_simple` | preferred Engine2D raster frame in a winit window | Simple's HTML layout → Engine2D preferred backend (`metal > cuda > rocm/hip > qualcomm > vulkan > opencl > opengl > intel > webgpu > software > cpu_simd > cpu`). No browser. |
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

The pure-Simple raster runs interpreted and is canvas-bound. It now resolves a
preferred backend by policy before raster: `SIMPLE_ENGINE2D_BACKEND` override
first, Metal on Darwin/macOS, CUDA/HIP when the standard visibility env vars are
present, then `software`. Explicit `software`, `cpu`, `cpu_simd`, or GPU backend
names remain available for deterministic comparison and fallback tests. Nine
O(n²)-class traps were
fixed (see `doc/08_tracking/bug/pure_simple_web_render_interpreter_bound_2026-06-06.md`):
1. heuristic-surface buffer built with a `push` loop → use `[0; w*h]` array-repeat;
2. the in-place array-write fix (`2d4579a0`) must be in the **running binary** —
   a stale `bin/simple` clones the framebuffer on every pixel write. Keep the
   driver current (rebuild on a stale deploy);
3. per-node stylesheet rescans in `compute_styles()` reparsed `<style>` blocks
   and rematched selectors before the extracted rule loop applied the same CSS
   again. The 2026-06-07 fix applies extracted rules directly; a 40-rule /
   40-node 96x96 smoke improved `2207027us -> 1259842us` with unchanged checksum
   `39575341662880`;
4. recursive layout child discovery scanned the full flat node arena for each
   container. The 2026-06-07 child-link fix builds `first_child`/`next_sibling`
   arrays once; a 180-sibling 96x96 smoke improved `494990us -> 472511us` with
   unchanged checksum `39574588256768`.
5. paint-time overflow clipping recomputed ancestor clip rectangles in each
   paint pass. The 2026-06-07 clip-cache fix builds per-node clip rectangles
   once per frame; a 48-deep overflow-hidden 96x96 smoke improved
   `974687us -> 867759us` with unchanged checksum `39575014374045`.
6. selector matching split/normalized every selector for every node, even for
   common single-class selectors. The 2026-06-07 selector fast-path avoids comma,
   child-combinator, and multi-class splitting when absent; an 80-rule / 80-node
   96x96 smoke improved `2361955us -> 2184205us` with unchanged checksum
   `39575341662880`. A follow-up single-class reject avoids padded-string
   construction/splitting for one-token class attributes that miss a `.class`
   selector, and skips compound `.a.b` selector splitting when the node has only
   one class token, while preserving exact class matching. The same selector
   path now extracts descendant/child-combinator complexity and rightmost-token
   filters once with the stylesheet rules, then uses that metadata before the
   full ancestor matcher so common misses do not pay per-node selector scans,
   normalization, or tree-walk cost.
7. single-property CSS declaration blocks still paid the full declaration
   lookup path for every matched rule. The 2026-06-07 declaration fast-path
   parses common one-property blocks once and falls back to the full parser for
   everything else; an 80-rule / 80-node 96x96 smoke improved
   `1783387us -> 1687064us` with unchanged checksum `182357384819455458`.
8. `FontRenderer.GlyphCache` linearly scanned the bounded glyph cache on every
   character before returning cached vector/bitmap glyphs. The 2026-06-07
   glyph-cache index adds hot-entry and `(codepoint,font_size)` bucket lookups;
   focused coverage proves repeated `A` and `A` after `B` reuse cached glyphs
   without another linear scan or accelerator attempt.
9. `TextBlitCache` still linearly scanned cached full-text buffers for
   non-adjacent repeated labels. The 2026-06-07 text-buffer cache index adds a
   `(text,fg,bg,font_size)` bucket lookup; focused coverage proves
   `Repeat, Other, Repeat` returns through `bucket_hits` without another cache
   scan.

The HTML layout Draw IR path now emits `text` commands for real text nodes with
font size, line height, glyph advance/scale, clip rect, parent id, and
`font-rendering=bitmap-vector-backend-preferred`. This gives native/GPU Draw IR
consumers a stable text contract before rasterization; the compatibility pixel
path still uses the pure-Simple 5x7 framebuffer rasterizer until a backend
consumes those text commands directly.
`engine2d_draw_ir_adv_*` now consumes the text contract by reading `font-size`,
rendering through FontRenderer-backed text blit buffers, and reporting
`font_offload_status`, `font_offload_reason`, `font_gpu_glyph_returned`, and
`font_production_ready` from the vector and bitmap font accelerator evidence.
A status such as `cpu-fallback` means routing and metadata are live while
production GPU dispatch is still missing; `gpu-glyph-returned` means the backend
rasterizer returned glyph pixels through the vector or bitmap evidence path.
The Draw IR text executor also reports `font_text_cache_hits` /
`font_text_cache_misses` for the per-batch text-blit buffer cache; repeated
identical labels hit a hot cache entry before scanning the cache list, avoiding
repeated glyph layout and blit preparation on common menu/list/status text.
Non-adjacent repeated labels use the text-buffer bucket index before any
fallback scan, so common GUI labels reused across separate windows or rows do
not pay an O(cache-size) lookup on every occurrence. When the full text payload
is already cached, Draw IR also skips repeat generated glyph staging/evidence
and reports the skip through `font_generated_args_cache_skips`.
Inside `FontRenderer`, glyph-level caching also has a hot entry and bucket index,
so repeated characters and recently used glyphs avoid a full glyph-cache scan
before vector or bitmap fallback/offload evidence is consulted.
Bitmap fallback follows the same evidence direction through
`rasterize_bitmap_accelerated()` and `bitmap_font_accelerator_stats()`: a
validated backend-returned bitmap glyph can bypass CPU mask generation and
record returned glyph/pixel counts. Bitmap returned-glyph probes scan slots
`0..7`, matching vector glyph probes, so a backend readback can provide multiple
glyphs for one text batch. The production backend priority remains host native
first, then generated GPU compute, then portable APIs, then CPU:
`metal > cuda > rocm/hip > qualcomm > vulkan > opencl > opengl > intel >
webgpu > software > cpu_simd > cpu`. `BackendProber.preferred_backend_order()`
and `probe_all_summary()` expose this exact sequence for diagnostics and CI
evidence. The vector and bitmap returned-glyph evidence slots follow the
native/generated subset of that order (`METAL`, `CUDA`, `ROCM`, `VULKAN`,
`OPENCL`) so a native or generated GPU glyph result wins before lower-priority
slots. Those slots now use one shared font backend priority helper for vector
and bitmap glyphs, while current bitmap/vector glyph tests prove the return
contract; live-kernel dispatch is proved backend by backend as each session
binds real launch args.
Generated glyph raster kernels share a validated argument packer for
`glyph_plan`, `dst`, `width`, `height`, and `font_size`; tests prove invalid
arguments fail closed, valid packed pointers round-trip, and generated glyph
launches now have an OpenCL backend-owned device staging smoke path. The OpenCL
facade allocates device `glyph_plan` and `dst`, packs those handles, launches
`simple_2d_glyph_raster_u32`, and requires readback evidence before reporting a
returned generated glyph. It still reports `production_ready=false` because the
smoke plan is not yet a real vector or bitmap glyph plan.
For bitmap glyphs, `OpenClBackend.launch_bitmap_glyph_raster_evidence()` and
`Engine2D.bitmap_glyph_raster_evidence()` now prepare the device `glyph_plan`
from the existing `rt_gui_get_glyph_8x16()` rows, so the OpenCL kernel consumes
real bitmap glyph row data instead of an opaque nonzero pointer. Successful
OpenCL bitmap readback now also carries grayscale glyph pixels and marks only
that bitmap path production-eligible inside the backend evidence.
Generated glyph provenance observes `args_ready`. OpenCL, CUDA, and ROCm session
launch evidence now use that shared layout validator before submit, so generated
glyph kernels do not treat an arbitrary nonzero pointer as launch-ready. Live
GUI text execution now uses the shared generated glyph staging helper to
allocate temporary glyph-plan/output buffers, packs a real args pointer for
GPU-routed Draw IR text, and reports `font_generated_args_ready` /
`font_generated_args_reason`. Draw IR also reports
`font_backend_glyph_status`, `font_backend_glyph_reason`, and
`font_backend_glyph_readback` from the Engine2D backend evidence bridge.
When a single-glyph bitmap command has production-ready OpenCL readback pixels,
Draw IR seeds them into `TextBlitCache` before normal `FontRenderer` rendering;
the rendered text payload still flows through the existing image blit path.
Repeated single-glyph labels are cache-gated before that backend probe, so a
glyph already present in `FontRenderer.GlyphCache` does not relaunch bitmap
readback evidence or invalidate text blit payloads again.
Multi-glyph backend readback batching remains the next production expansion.
`web_render_vector_font_native_compute_evidence()` mirrors the same native-first
order for shared web-render reports, while the older CUDA/OpenCL-only evidence
helper remains available for existing reports.
Custom Engine2D priority lists use the same canonicalization as strict backend
selection, so aliases such as `hip` and `simd_cpu` select `rocm` and `cpu_simd`
instead of falling through to plain CPU.

Keep pure_simple viewports modest (≤ ~400 wide); chromium opens a live window
and is unaffected.

## Honest comparison (no memorized pixels)

Use two **independently produced** artifacts + an absolute oracle, never hard-coded
captured pixels. Gate: `scripts/check/check-electron-simple-web-engine2d-bitmap-evidence.shs`
(pure-Simple Engine2D vs real Chromium OSR → `mismatch_count=0`).

See also: [`web_render_backend_tldr.md`](web_render_backend_tldr.md).

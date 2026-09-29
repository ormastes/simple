# TL;DR — CPU<->GPU boundary census, Simple 2D + web renderer (2026-09-11)

Full census: `cpu_gpu_boundary_census_2026-09-11.md`. Diagnosis only, nothing fixed.
Model frame: 3840x2160 (8.29M px / 33.2 MB), ~2000 nodes, ~5000 glyphs.

1. **Full-frame readback is the renderer's API.** `simple_web_renderer.spl:89-99`
   returns `[u32]`; `web_render_file_gui.spl:129-140` downloads 33 MB, scans all
   8.29M px on the CPU (`varied_nonzero_count:48-61`), then re-uploads via
   winit — while `_present_device` (`backend_vulkan.spl:1319`) could present the
   device buffer with damage rects and zero host traffic.
2. **The A/B sampler re-arms on every scene change.** `_web_draw_ir_key` keys on
   `composition.generation` (`simple_web_layout_engine2d_fast.spl:400-411`), so
   scroll/animation/tab-switch frames each re-run 3 sampling frames of
   software-raster + upload + GPU + 2 readbacks + 2x8.29M pixel compares
   (`:854-874`).
3. **Exact CPU pixel equality authorizes GPU use** (`:791-812`, gate at
   `simple_web_html_engine2d_presenter.spl:314-321`) — 8.29M compares per
   revalidated frame; if the gate never passes, every steady frame is the
   software oracle (`:851-856`) even on a healthy Vulkan device.
4. **Per-node clip kills the GPU text lane.** `draw_ir_adv.spl:3539,3808,4053`
   set a scissor per box; `backend_vulkan_font.spl:569` then blocks the packed
   glyph dispatch, so `draw_text` (`backend_vulkan.spl:1034-1039`) CPU-rasters
   and uploads each run — ~5000 glyphs' worth.
5. **Batching defeated by two mid-frame fence waits:** 256-entry descriptor cap
   (`backend_vulkan.spl:413`) and the `draw_text_bg` whole-batch flush
   (`backend_vulkan_font.spl:690-703`), both -> `submit_and_wait_fence`
   (`backend_vulkan_helpers.spl:418`); `emu_*` scanline expansion
   (`backend_emu.spl:463-490`) multiplies the dispatch count that trips it.

Cleared: `read_pixels` uses a native memcpy; Vulkan present is device-side only
(`vulkan/swapchain.rs:676`), no map/wait/readback.

CPU-regardless-of-env: `web_render_page_ppm.spl:45` hardcodes `cpu_simd`;
probe failure -> `"software"` silently (`simple_web_engine2d_renderer.spl:1248-1252`);
only `SIMPLE_GUI_BACKEND` is ever read, never `SIMPLE_2D_BACKEND`.

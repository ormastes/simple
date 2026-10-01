# CPU<->GPU boundary census — Simple 2D engine + web renderer (2026-09-11)

Diagnosis only; nothing fixed. Model workload: 3840x2160 (8,294,400 px = 33.2 MB
at 4 B/px), ~2000 layout nodes, ~5000 glyphs, steady interactive frame.
Classes: **(a)** CPU work with a GPU op available, **(b)** GPU->CPU readback,
**(c)** CPU->GPU upload, **(d)** sync/wait, **(e)** per-frame allocation.
Counts are derived from loop structure, not measured on this host.

## Ranked census

| # | file:line | what crosses | per 4K frame | class | GPU alternative in-module? |
|---|---|---|---|---|---|
| 1 | `examples/06_io/ui/web_render_file_gui.spl:48-61,129-140` | `varied_nonzero_count(pixels)` — interpreted loop over the whole readback, run on EVERY input-driven redraw as an acceptance check | 8,294,400 iterations | a | yes — `Engine2DReadback.checksum` is already computed device-side and returned in the same struct (`backend_vulkan.spl:1613`) |
| 2 | `simple_web_layout_engine2d_fast.spl:854-874` (`_web_draw_ir_choose_route` sampling branch) + `:400-411` (`_web_draw_ir_key` keys on `composition.generation`) | every scene mutation = new cache key = 3 fresh sampling frames, each running BOTH routes: full software CPU raster + 33 MB upload + 33 MB readback, then full GPU render + 33 MB readback, then 2 full-frame equality scans | per changed frame x3: 2x8.29M compare iters + 2 readbacks (66 MB) + 1 upload (33 MB) + 1 full CPU raster | a,b,c | yes — the GPU route alone (`:721`) produces the same pixels |
| 3 | `simple_web_layout_engine2d_fast.spl:806-810` (steady offload branch, cache miss) | `_web_draw_ir_pixels_equal(gpu.readback.pixels, state.validated_pixels)` — exact per-pixel revalidation against a retained CPU oracle, plus the readback that feeds it | 8,294,400 compare iters + 33 MB readback | a,b | yes — device checksum already carried on the readback |
| 4 | `backend_vulkan.spl:1034-1039` via `backend_vulkan_font.spl:569-570` (`clip-unsupported-by-font-composite`) and Draw IR `draw_ir_adv.spl:3539,3808,4053` setting a clip per clipped node | any clipped/masked/non-opaque text run leaves the atlas lane: `text_blit_buffer` CPU-rasters the run, then `draw_image_blend` uploads it | up to 2000 CPU rasters + 2000 image uploads | a,c | yes — the packed font-atlas compute dispatch in the same module (`backend_vulkan_font.spl:839-893`) is skipped, not used |
| 5 | `backend_vulkan_font.spl:690-703` (`_bitmap_text_bg_atlas_path`, TODO already filed in-source) | `draw_text_bg` flushes the WHOLE pending batch = `vulkan_sffi_submit_and_wait_fence` (`backend_vulkan_helpers.spl:418`) before each background band | 1 submit+fence-wait per background-text draw; up to ~2000 | d | partially — needs `vulkan_sffi_pipeline_barrier`, which does not exist (0 `barrier` call sites under `src/lib/**/engine2d`) |
| 6 | `backend_vulkan.spl:413,697` (`pending_compute_descriptors: [0i64; 256]`) + `backend_vulkan_helpers.spl:481-488,510-513` | the batched command buffer holds only 256 dispatches; overflow forces `_flush_pending_compute()` = submit + fence wait mid-frame | >=8 fence waits for 2000 rects, far more once emu_* expansion (row 7) multiplies the rect count | d | no — the cap is the batch design |
| 7 | `backend_emu.spl:463-490` (`emu_draw_ellipse_filled`; same shape for `emu_draw_arc`, `emu_draw_bezier`, `emu_draw_polygon_filled`, `emu_draw_rounded_rect_outline`, `emu_draw_rect_thick`), reached from `backend_vulkan.spl:1650-1683` | each such primitive expands to ~2*ry `draw_rect_filled` calls, i.e. one compute dispatch + one descriptor set per scanline | rounded corners/ellipses on ~2000 nodes: hundreds to thousands of extra dispatches | a,e | no — no ellipse/bezier compute pipeline exists in the Vulkan backend |
| 8 | `backend_vulkan_font.spl:641` (`atlas_pixels: vulkan_bitmap_font_atlas_pixels(...)` built unconditionally per call) + `:476-515` nested per-subpixel loops | the full 95-cell coverage atlas is CPU-rasterized on EVERY `draw_text`, then discarded by the generation cache at `:820` | 1 atlas raster per text run (~2000); GPU upload itself IS cached | a,e | n/a — the cache exists one layer too late; hoist the build behind the same identity check |
| 9 | `backend_vulkan_helpers.spl:525` (`vulkan_sffi_create_descriptor_set(pipe)` per enqueued primitive) | a fresh descriptor set per draw call; only the FONT params buffers are pooled (`backend_vulkan_font.spl:846-861`) | 1 descriptor alloc per primitive (>=2000) | e | yes — the font lane's `font_params_pool` / `font_descriptor_pool` shows the pooling pattern |
| 10 | `backend_vulkan.spl:1170-1207` (`draw_image` host fallback) | on native-composite failure: full framebuffer readback, per-pixel CPU clip/mask/copy, then full-frame upload | per failing image: 33 MB down + w*h CPU iters + 33 MB up | a,b,c | yes — `_draw_image_composite_native` (`:1041`) is the GPU op that just failed |
| 11 | `backend_vulkan.spl:1689-1700+` (`draw_gradient_rect_h` with a mask) | mask-active gradients are computed per pixel on the CPU | w*h iters per gradient node | a | yes — `_pack_gradient_pc` gradient pipeline exists but is bypassed when a mask is set |
| 12 | `simple_web_engine2d_renderer.spl:1191-1196` (accent-stripe heuristic) | one 1px-wide `draw_rect_filled` every 17 px across the viewport | 226 dispatches at 3840 px wide | e | yes — one rect-list/packed dispatch |
| 13 | `simple_web_engine2d_renderer.spl:1200-1202` | heuristic lane: `engine.read_pixels()` then `engine.shutdown()` — full readback + device teardown per render call | 33 MB + full backend teardown per frame | b,e | yes — `_web_fast_engine_slots` parking (`simple_web_layout_engine2d_fast.spl:290-333`) exists but only for the Draw IR lane |
| 14 | `examples/06_io/ui/web_render_page_ppm.spl:45` | backend hardcoded to `"cpu_simd"`; the whole entry is CPU | all of it | a | yes (see fallbacks below) |

**Not a defect (checked, clearing prior suspicion):** `read_pixels_with_source`
(`backend_vulkan.spl:1620-1628`) now uses `vulkan_sffi_copy_u32_into`, a native
memcpy, not the old per-pixel loop. Present is device-side only —
`rt_vulkan_present_buffer` -> `copy_buffer_and_present` ->
`cmd_copy_buffer_to_image` (`src/compiler_rust/runtime/src/vulkan/swapchain.rs:676`);
no `vkMapMemory` / `wait_for_fences` / `device_wait_idle` on the present path.
`_web_draw_ir_pixel_fingerprint` (`:627-637`) is a retained diagnostic seam with
no hot caller.

## Top 5 root causes, with the exact loop each sits in

1. **The web renderer's public contract is "HTML -> `[u32]`", so every frame is a
   full-frame readback by construction.** `simple_web_renderer.spl:89-99` ->
   `_render_engine2d_surface_pixels`; the interactive consumer
   `web_render_file_gui.spl:129-140` then hands those host pixels to
   `winit_present_rgba_u32`, so a Vulkan-rendered 4K frame is downloaded (33 MB),
   scanned twice on the CPU (rows 1 and 3), and re-uploaded to the window —
   while `_present_device` / `vulkan_sffi_present_buffer_regions`
   (`backend_vulkan.spl:1319-1332`) can present the same device buffer with zero
   host traffic and damage rects.
2. **`_web_draw_ir_key` includes `composition.generation`**
   (`simple_web_layout_engine2d_fast.spl:400-411`), so the A/B sampler's
   "first 3 frames" cost is re-paid on every scroll, animation tick and tab
   switch — precisely the interactive frames. The loop is
   `_web_draw_ir_choose_route:854-874`, which runs `_web_draw_ir_upload_route`
   AND `_web_draw_ir_gpu_route` in the same frame and then calls
   `_web_draw_ir_pixels_equal` twice over 8.29M pixels (`:589-596`).
3. **Exact CPU pixel comparison is the authorization mechanism for using the
   GPU at all.** `_web_draw_ir_choose_route:791-812` re-validates the GPU frame
   against a retained software oracle pixel-for-pixel on every device/surface
   token change, and `web_gpu_paint_timing_evidence`
   (`simple_web_html_engine2d_presenter.spl:314-321`) requires
   `pixels_match and upload_device_proven and gpu_device_proven` before
   `should_offload` can ever be true. Correctness gate, per-frame CPU price.
4. **Clip is per node, and clip disables the GPU text lane.** The Draw IR
   executor sets a scissor per clipped box (`draw_ir_adv.spl:3539,3808,4053`);
   `vulkan_bitmap_text_atlas_block_reason:569-570` then returns
   `clip-unsupported-by-font-composite`, so `draw_text`
   (`backend_vulkan.spl:1034-1039`) CPU-rasters the run and uploads it as an
   image. On a clipped 4K page essentially all ~5000 glyphs take the CPU path
   despite a working packed-glyph compute dispatch in the same module.
5. **Frame batching is defeated by two mid-frame fence waits.** The 256-entry
   `pending_compute_descriptors` table (`backend_vulkan.spl:413`) and the
   `draw_text_bg` whole-batch flush (`backend_vulkan_font.spl:690-703`) each
   call `_flush_pending_compute` -> `vulkan_sffi_submit_and_wait_fence`
   (`backend_vulkan_helpers.spl:418`), turning the intended one-submit-per-frame
   into tens-to-thousands of blocking submissions — and emu_* scanline expansion
   (`backend_emu.spl:463-490`) inflates the dispatch count that trips the cap.

## Where the web renderer takes CPU regardless of `SIMPLE_2D_BACKEND`

- **Hardcoded at the entry.** `web_render_page_ppm.spl:45` passes `"cpu_simd"`
  literally; no env is consulted. `web_engine2d_gui.spl:73` likewise. Only
  `web_render_file_gui.spl:44-46` reads an env var, and it is
  `SIMPLE_GUI_BACKEND`, not `SIMPLE_2D_BACKEND`.
- **Probe failure silently downgrades to `"software"`.**
  `simple_web_engine2d_renderer.spl:1248-1252`: any non-cpu name that fails
  `Engine2D.probe_backend` returns `"software"` with no error to the caller.
- **The offload decision can latch CPU forever.** If `should_offload` is false
  (`presenter.spl:321` — needs both routes device-proven, pixels equal, and
  `gpu_p95 + WEB_GPU_PAINT_MIN_MARGIN_US < upload_p95`), the steady branch at
  `simple_web_layout_engine2d_fast.spl:851-856` runs `_web_draw_ir_oracle_route`,
  a pure software render, on every subsequent frame of that key — even with a
  healthy probed Vulkan device.
- **Feature gaps route per primitive, not per frame:** clip/mask/non-opaque text
  (`backend_vulkan_font.spl:569-573`), masked gradients
  (`backend_vulkan.spl:1692`), and every `emu_*` primitive
  (`backend_vulkan.spl:1650-1683`) fall to CPU individually with the backend
  still nominally Vulkan — `mark_cpu_fallback` records it, nothing re-routes.

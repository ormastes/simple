# 2D rendering slowness: DMA / wordline alignment / SoA / async — evidence-based answers

- **Date:** 2026-09-02
- **Question:** why is 2D rendering slow? Hypotheses: no DMA use, wordline/row
  alignment miss, no struct-of-arrays, no async/future/promise.
- **Scope:** software 2D lane (`hosts/scene_raster.spl`), Metal + Vulkan
  Engine2D lanes (`src/lib/gc_async_mut/gpu/engine2d/`, Rust runtime).

## Verdict per hypothesis

| Hypothesis | Verdict |
|---|---|
| No DMA | Half right. Metal uses `StorageModeShared` unified memory + memcpy — correct, no DMA needed on Apple silicon. Vulkan is *worse* than no-DMA: every transfer allocates a fresh staging buffer and blocks on a fence; device-to-device copies go GPU→CPU→GPU (`vulkan_graphics_runtime_buffer.rs:547-576`). |
| Wordline/row alignment miss | **Not the bottleneck.** The 2D path uses storage buffers + push constants, not textures — there is no `bytesPerRow` in play. Swapchain copy rows are tightly packed and valid (`vulkan/swapchain.rs:657-658`). |
| No SoA | Partially right, second-order. `DrawIrCommand` is a 19-field AoS struct (`draw_ir.spl:68-87`), materialized per command per frame in the interpreter. DrawIrV3 is SoA flat columns, but its accessors re-allocate view structs per command (`draw_ir_v3.spl:483-494`). Costs real interpreter time, but small next to submission/readback. |
| No async/future/promise | **Right.** The render path has zero async. Metal: `command.waitUntilCompleted()` per primitive (`metal_graphics_runtime.rs:159`). Vulkan: `fence.wait(u64::MAX)` per transfer (`vulkan/device.rs:939`). Simple *has* a monoio-based async executor (`src/lib/nogc_async_mut/async*.spl`, `rt_monoio_future_*`) — unused by rendering, and GPU completion isn't an io_uring event, so bridging needs Metal `addCompletedHandler` / fence polling, not the existing IO executor. |

## The real cost ranking (measured/observed)

1. **Per-primitive commit + blocking wait (Metal).** No frame batching:
   every rect/line/image does command buffer → encoder → commit →
   `waitUntilCompleted` (`backend_metal.spl:2019-2105`), ~10 ms fixed cost
   each, CPU and GPU fully serialized. The font fix batched only font quads
   (360→30 submissions/frame); all other primitives still pay one round trip
   each.
2. **Full-frame GPU→CPU readback every frame, even for display.**
   `draw_ir_adv.spl:2767,3214-3220` unconditionally reads the framebuffer
   back; the Metal GUI app then CPU-presents via `winit_present_rgba`
   (`gui_metal.spl:80-135`) — GPU as offscreen rasterizer with a full
   round-trip per frame. Metal pixel extraction is a per-8-byte FFI loop
   (`backend_metal.spl:1108-1116`; in-code comment: ~1.4 s at 1024×768, 90 s+
   at Retina) plus an interpreted O(n) checksum (`backend.spl:17-23`). A
   no-readback path exists (`present_window_device`) but showcase/capture
   lanes don't use it.
3. **Translucent rect → CPU array + image upload.** `backend_vulkan.spl:794-802`:
   `pixels: [u32] = [color; w*h]` then `draw_image_blend` — the glass theme is
   mostly translucent rects, so every rect is a CPU fill + staging alloc +
   blocking transfer instead of a shader fill with alpha.
4. **Vulkan image-fallback full-frame round trip per image**
   (`backend_vulkan.spl:1051-1085`): download whole FB, host-blend, re-upload.
5. **Per-pixel interpreted marshalling on every transfer:**
   `_pixels_to_bytes`/`_bytes_to_pixel_array` (`backend_vulkan_helpers.spl:641-669`),
   Metal per-pixel FFI loops (`backend_metal.spl:1359-1362,1591-1596`,
   ~480K FFI calls for one 800×600 frame) — one-call externs exist but are
   opt-in (`SIMPLE_ONE_CALL_UPLOAD`/`SIMPLE_ONE_CALL_READBACK`).
6. **Software lane: interpreted per-pixel rasterizer.** `scene_raster.spl`
   `put` per pixel with full guard set (`:89-121`), surface init/clear one
   `push` per pixel (`:55-87`), PPM capture 3 pushes/pixel (`:285-301`), TTF
   raster = one FFI call + one push per pixel (`font_rasterizer.spl:110-127`).
   The faster `SoftwareBackend` span machinery exists but is unused by the
   showcase host.

## Fix directions, in order

1. Batch ALL primitives per frame into one command buffer; one fence per
   frame (extends the font-quad fix pattern to rect/line/image).
2. Frames in flight (2-3): submit frame N, wait only on frame N-2's fence —
   this is where "async" actually belongs for GPU: completion handlers /
   non-blocking fence polls, not per-primitive futures. Async around 360
   submissions is still 360 submissions; batching comes first.
3. No readback in the display path: present on-GPU (`present_window_device`);
   keep readback for capture/CI lanes only, and make the one-call readback
   the default.
4. Alpha-rect compute shader (kill the `[color; w*h]` + image-upload detour).
5. Software lane: route the host through span primitives, preallocate with
   `[v; n]`, bulk PPM encode.

Related: `doc/08_tracking/bug/engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14.md`,
and the (since-removed) `doc/01_research/local/metal_2d_frame_cost_perf.md`
conclusion from commit 27f6ae9a892: "submission overhead, not architecture".

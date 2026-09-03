# Domain research: how production 2D renderers structure GPU work

- **Date:** 2026-09-03
- **Pairs with:** `doc/01_research/local/2d_rendering_perf_dma_alignment_soa_async.md`
  (the local evidence: per-primitive commit+wait, per-frame full readback,
  CPU pixel arrays for alpha rects, per-primitive buffer allocation)
- **Question:** how do Skia/Vello/ImGui/browsers/game engines solve batching,
  buffer movement, alpha offload, and readback — and what should Simple's
  Engine2D adopt?

## 1. Batching: one submission per frame; draw calls split only on state change

- **Dear ImGui**: all draw lists memcpy'd into ONE vertex + ONE index buffer
  per frame; one `drawIndexedPrimitives` per texture/clip change. README:
  "A common misunderstanding is to mistake immediate mode GUI for immediate
  mode rendering." (imgui_impl_metal.mm; docs/BACKENDS.md)
- **Skia Graphite**: deferred `Recording`s submitted once per frame; opaque
  draws reordered to minimize state changes, depth buffer preserves
  correctness (blog.google/chromium, Jul 2025).
- **Vello**: whole scene encoded once into flat GPU buffers; one multi-stage
  compute pipeline per frame. "As much work as possible is offloaded to the
  GPU." (Raph Levien, "Fast 2D rendering on GPU", 2020)
- **Chrome viz**: display lists → GPU texture tiles → one aggregated
  compositor frame (RenderingNG architecture, developer.chrome.com).

## 2. Buffer movement: frames-in-flight ring + per-frame bump arenas

- **Apple Metal Best Practices**: triple buffering — FIFO of 3 buffers +
  semaphore; CPU writes frame n+1 while GPU reads n; `addCompletedHandler`
  (callback, NOT waitUntilCompleted) unlocks reuse. "Avoid creating new
  resources during a render or compute loop, even for dynamic data."
  Small fully-dirty per-frame data → `MTLStorageModeShared` (zero-copy on
  unified memory).
- **Vulkan**: `MAX_FRAMES_IN_FLIGHT = 2-3`, per-frame fences; per-buffer
  `vkAllocateMemory` explicitly wrong (`maxMemoryAllocationCount` may be 4096)
  → suballocate from big blocks; VMA ring-buffer pools (used by Skia,
  Filament, Godot, Blender).
- **ImGui Metal backend**: reusable `MetalBuffer` pool, returned in
  `addCompletedHandler`, purged after ~1s idle.

## 3. Alpha/translucency: pipeline blend state, never CPU pixel arrays

- ImGui Metal: `SRC_ALPHA`/`ONE_MINUS_SRC_ALPHA` fixed-function blending;
  alpha rides in the vertex color of an ordinary batched quad. Canonical
  backend setup: "alpha-blending enabled, no depth testing, scissor enabled."
- Vello: blending in the fine-raster compute kernel. Skia Graphite: GPU
  blending back-to-front. No fetched production renderer allocates CPU pixel
  arrays for alpha rects.

## 4. Readback: display never reads back; capture reads back async, N frames late

- Display path presents on-GPU (drawable/swapchain); Metal
  `synchronizeResource:` updates CPU copies after command-buffer completion.
- WebGL2 best practices (MDN): synchronous `readPixels()` = finish +
  round-trip; instead read into PIXEL_PACK_BUFFER, `fenceSync`, poll
  `clientWaitSync` timeout 0, consume later (`readPixelsAsync` pattern).
- Chrome RenderingNG: raster completion tracked with sync tokens; "Chromium
  often doesn't wait for raster to complete."

## 5. CPU-side: flat encoding + caching + damage

- Vello: static scene fragments retained and stitched; glyphs render at any
  size without CPU re-encoding (GPU flattening).
- Flutter Impeller: ALL shader compilation offline at build time; glyph runs
  into texture atlases; caching explicit.
- Chrome: pre-paint invalidates only changed tiles; scroll/animation skip
  paint entirely (compositor thread, multiple buffering).
- Flutter framework: persistent element tree; only changed widgets rebuild.

## Cross-cutting constants

2-3 frames in flight; one command buffer per frame; per-frame bump arenas in
persistently mapped memory; alpha via blend state; readback fence/callback
and delayed. Every one of Engine2D's four current behaviors contradicts an
explicit, sourced best practice above.

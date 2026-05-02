# Drawing-Stack Out-of-Scope Register

**Updated:** 2026-04-15

This register documents items intentionally deferred from the Chromium-mirror drawing stack landed in Waves 1–3. Each entry states *what* is missing, *why* it was deferred, and *what would be needed* to land it later.

---

## 1. WebGL / WebGL2 / WebGPU

- **Chromium component:** `gpu::gles2::GLES2Implementation`, `gpu::webgpu`
- **Why deferred:** ANGLE-equivalent translation layer is multi-month effort; Vulkan backend (W2-1d) lands the pipeline cache + command buffer record but not the WebGL shader-source → SPIR-V path or the ES context.
- **Future blocker:** Need a real GLSL/WGSL parser + SPIR-V emitter. Cross-cuts with the Skia GPU backend (already partial).
- **Scope file (when landed):** `src/lib/skia/backend/webgl/`, `src/lib/skia/backend/webgpu/`.

## 2. Video decode + VideoDrawQuad pipeline

- **Chromium component:** `media::VideoDecoder`, `viz::VideoHoleDrawQuad`, `viz::YUVVideoDrawQuad`
- **Why deferred:** Requires codec FFI Simple does not currently expose (libavcodec, VAAPI, NVDEC, MediaFoundation). DrawQuad enum has placeholder variants but the YUV resampling, gamma, and color-conversion chain is unimplemented.
- **Future blocker:** SFFI bindings for libavcodec or hardware-decoder ioctls; YUV→RGB shader path in CPU and Vulkan backends.
- **Scope file (when landed):** `src/lib/media/video_decoder.spl`, `src/lib/viz/feature/video_resource_updater.spl`.

## 3. HDR / Display-P3 / ICC color management

- **Chromium component:** `gfx::ColorSpace`, `SkColorSpace`, `cc::ColorSpaceConverter`
- **Why deferred:** All current Skia ops use sRGB-premul implicitly. HDR requires float pixel buffers, tone-mapping operators, and per-display ICC profiles — none of which the current Bitmap (`[u8]` RGBA premul) supports.
- **Future blocker:** Extend Bitmap with optional `SkColorSpace` field; add f16/f32 pixel buffer variants; integrate ICC profile parser.
- **Scope file (when landed):** `src/lib/skia/entity/color_space.spl`, `src/lib/skia/feature/color_management/`.

## 4. Metal backend (macOS) and Direct3D 12 backend (Windows)

- **Chromium component:** `GrMtlGpu`, `GrD3DGpu`
- **Why deferred:** Simple's primary target is x86_64 QEMU + SimpleOS; Metal/D3D require platform-specific syscalls Simple doesn't bind. Vulkan backend (W2-1d) is the canonical GPU path for now.
- **Future blocker:** Platform-specific FFI bindings; new backend modules cloning the Vulkan PipelineKey + CommandBufferRecord pattern.
- **Scope file (when landed):** `src/lib/skia/backend/metal/`, `src/lib/skia/backend/d3d12/`.

## 5. Real threaded compositor

- **Chromium component:** `cc::Scheduler`, impl-thread + main-thread split, `cc::ProxyImpl`
- **Why deferred:** Simple's compositor (`LayerTreeHost.commit`) currently does deep-copy synchronously in one capsule. A true threaded compositor needs the impl-thread on a separate capsule, with capability-gated IPC for commits, plus the BeginFrameSource/scheduler driving frame production.
- **Future blocker:** Async runtime integration for Simple capsules; `BeginFrameSource` stub and a frame-pacing scheduler.
- **Scope file (when landed):** `src/lib/cc/feature/scheduler.spl`, `src/lib/cc/feature/proxy_impl.spl`.

## 6. Full COLRv1 color emoji paint-graph composition

- **Chromium component:** `SkColorFontPriv`, COLRv1 PaintComposite/PaintColrLayers full traversal
- **Why deferred:** W3-3f landed the table parser + layer-list decoder + PaintKind enum + format-byte dispatcher with safe `Solid` fallback, but the paint-graph composition (transforms, gradients, composite modes per layer) is `pass_todo` inline. Full implementation needs the radial/sweep gradient eval to integrate with the glyph rasterizer.
- **Future blocker:** Tie `decode_paint_subtable` paint-graph nodes to the existing `eval_*_gradient` (`shaders.spl`) and `compose` (`blend_compose.spl`) helpers; add per-layer raster.
- **Scope file (when landed):** extend `src/lib/skia/feature/glyph/colrv1.spl` with `compose_paint_graph(blob, paint_offset) -> Bitmap`.

## 7. Variable fonts — full HarfBuzz-equivalent variation

- **Chromium component:** `HarfBuzzShaper` with `hb_font_set_variations`, `gvar` glyph-delta interpolation
- **Why deferred:** W1-3a `parse_fvar_axes` reads axes; `parse_avar_mapping` returns the normalized coordinate unchanged (no avar segment-map interpolation). `gvar` glyph-delta application is not implemented — variable-font glyph outlines render at default master only.
- **Future blocker:** Implement `avar` segment-map interpolation; parse `gvar` table and apply per-glyph deltas to outline points before rasterization.
- **Scope file (when landed):** extend `src/lib/skia/feature/glyph/ot_parser.spl` with `parse_gvar`, `apply_glyph_deltas`.

## 8. Real pixel-perfect Chromium reference comparison

- **Chromium component:** headless Chrome screenshot capture for golden PNGs
- **Why deferred:** W3-8d landed self-goldens (each scene rasters its own minimal SkPicture once and freezes the bitmap). Self-golden contract proves *determinism* across runs but does NOT prove *parity with real Chromium pixels*. Real reference capture requires running headless Chrome 124 + a per-scene URL fixture + image diffing.
- **Future blocker:** Headless-Chrome harness in CI; per-scene HTML/CSS fixture mirroring the SkPictureOps; image diff threshold tuning.
- **Scope file (when landed):** `test/reftest/parity/chromium_refs/<scene>.png` + `tools/capture_chromium_refs.shs`.

## 9. Browser-tree restructure (`examples/browser/` → `src/lib/{content,gui}/browser_app/`)

- **Why deferred:** The plan called for a mechanical move of the entire `examples/browser/` tree (50+ `.spl` files across entity/feature subdirs) into the canonical `src/lib/content/` and `src/lib/gui/` namespaces. Active upstream work (recent commits including TabManager render-loop integration and DevTools attach) is concurrently editing files under `examples/browser/`. Performing this move in the renderer worktree would conflict with parallel browser work and potentially clobber in-flight changes.
- **Future blocker:** Coordinate a quiet window where `examples/browser/` has no active feature work; stage the move as a single atomic commit with import-rewrite via Grep+Edit; verify all downstream callers compile.
- **Scope file (when landed):** `git mv` per file, then `Grep` + `Edit` to rewrite `use examples.browser.X` → `use std.{content,gui}.browser_app.X`.

## 10. Real CPU vs Vulkan parity testing

- **Why deferred:** W2-1d Vulkan backend lands pipeline cache + triangulation + CommandBufferRecord, but the actual `vkQueueSubmit` + framebuffer readback path is `pass_todo` (no GPU ioctl bindings in current Simple runtime). The CPU vs Vulkan delta table in `drawing_parity_matrix.md` Section 8 is therefore aspirational — both backends produce data structures, but only CPU produces real pixels.
- **Future blocker:** SFFI bindings for `vkCreateInstance`, `vkAcquireNextImageKHR`, `vkQueueSubmit`, framebuffer mapping; Vulkan validation-layer integration for catching pipeline mismatches.
- **Scope file (when landed):** `src/lib/skia/backend/vulkan/submit.spl`, `src/runtime/vulkan_ffi.spl`.

## 11. Ink Overflow / CSS Masking, CSS Container Queries, WebXR

- **Chromium components:** `blink::MaskPainter`, `blink::ContainerQueryEvaluator`, `device::mojom::XRDevice`
- **Why deferred:** Out of the renderer drawing-stack scope. These are Blink-layer features driven by CSS or by hardware capabilities Simple does not bind. They require the layout + style-recalc passes (which are themselves stubbed).
- **Future blocker:** Full Blink layout tree implementation; CSS parser extension for container queries; WebXR device-API layer.

---

## How to update this register

When a deferred item lands:
1. Delete the entry here.
2. Flip the corresponding row in `drawing_parity_matrix.md` Section 9 from ❌/🟢 to ✅.
3. Reference the implementing commit in the matrix.

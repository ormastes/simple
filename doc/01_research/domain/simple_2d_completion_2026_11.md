# Domain Research: Simple 2D Completion (Skia CPU & Vulkan/MoltenVK)

- **Date:** 2026-11-28
- **Scope:** Analytical scanline AA, `saveLayer` offscreen isolation & Porter-Duff compositing in Skia; Vulkan sub-rect staging/readback, damage-bounded GPU blending, and macOS MoltenVK compatibility.

---

## 1. Skia Analytical Scanline Coverage AA & `saveLayer` / Porter-Duff Compositing

### 1.1 Analytical Scanline Coverage AA (`SkScan_AAAPath`)
- **Exact Pixel Area / Subpixel Edge Tracking:** Modern Skia CPU rasterization (`SkScan_AAAPath`) computes fractional pixel coverage from edge crossings along scanlines, clamping accumulated winding/parity coverage in `[0, 1]` and emitting coverage runs to the blitter (`SkRasterPipelineBlitter::blitAntiH`) rather than mutating destination pixels multiple times per scanline.
- **Simple Status Match:** `src/lib/skia/backend/cpu/raster_prims.spl` (`fill_path_aa`, L440-564) already implements fractional edge records (`_Edge`), 4-subrow scanline sampling, horizontal span overlap accumulation into `cov`, and single-blend output per pixel.
- **Coverage x Blend Mode Interaction:** In Skia, coverage (`alpha_mask`) modulates the *composited result* as `lerp(dst, compose(src, dst, mode), cov)` (i.e. coverage-weighted blending) rather than scaling `src.a` before Porter-Duff `Src` / `DstIn` / `Clear` / `Xor` (scaling `src.a` before `Clear` or `Src` produces incorrect partial-coverage halos because `Src` with `alpha = cov * sa` overwrites destination instead of interpolating between `dst` and `src`).
  - **Gap in Simple Skia CPU:** `_fill_rect_mode` (`backend.spl:149-160`) ignores fractional coverage completely (pixel-center test only), and `DrawRRect`/`DrawOval`/`DrawPath`/`DrawImage`/`DrawPaint` ignore `SkBlendMode`.

### 1.2 `saveLayer` Offscreen Allocation & Restore Compositing
- **Canonical Skia Semantics:**
  1. `saveLayer(bounds, paint)` pushes an offscreen bitmap/surface sized to the intersection of `bounds` (if present, transformed to device space) and the current `clip` (quick-reject if empty).
  2. The offscreen layer starts **transparent black `(0, 0, 0, 0)`** in premultiplied RGBA, with its clip/transform translated to layer-local origin `(layer_x, layer_y)` (or kept in device space with offset indexing).
  3. All child draw calls inside the layer render into the offscreen bitmap using each child's own `SkPaint.blend_mode` (isolated from the parent framebuffer!).
  4. `restore()` pops the offscreen layer and composites it **once** onto the parent layer/surface using the saved layer paint's `alpha` and `blend_mode` (`compose(layer_px * layer_alpha, parent_px, layer_mode)`).
- **Why Inline `CanvasState.mode` Propagation Fails:** Passing `saveLayer.paint.blend_mode` down to child draws (`backend.spl:127-131, 228, 308`) causes overlapping children to blend with *each other* using the layer's mode (e.g., `Multiply` or `DstIn` inside the layer corrupts internal overlaps and produces wrong group opacity). `opacity_layer` and `backdrop_filter` / `porter_duff` / `mix_blend_mode` parity require real offscreen `saveLayer` isolation.

---

## 2. Vulkan Sub-Rect Staging/Readback, Damage-Bounded Blending & MoltenVK Compatibility

### 2.1 Sub-Rect Buffer/Image Transfers & MoltenVK Alignment
- **Row Pitch & Alignment (`VkBufferImageCopy`):** Under Vulkan on macOS via **MoltenVK** (`MTLBlitCommandEncoder`), sub-rectangle buffer/image copies (`vkCmdCopyImageToBuffer` / `vkCmdCopyBufferToImage`) require `bufferRowLength` / `bufferImageHeight` to reflect the container stride and prefer 4-byte-aligned row pitches/offsets (satisfied naturally by `RGBA8`/`ARGB8` 4-byte pixels, though arbitrary unaligned offsets or non-coherent staging buffers can trigger Metal hazard or column-offset bugs).
- **Image Layout & Barriers:** Source targets must transition to `VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL` with `VK_ACCESS_TRANSFER_READ_BIT` after render/compute writes (`COLOR_ATTACHMENT_OPTIMAL` or compute shader write) before copy/readback; missing barriers on MoltenVK cause stale or torn readbacks because Metal relies on Vulkan barriers to emit `MTLComputeCommandEncoder` / `MTLBlitCommandEncoder` memory synchronization.
- **Coherency (`HOST_VISIBLE | HOST_COHERENT`):** Using `HOST_VISIBLE | HOST_COHERENT` staging buffers maps cleanly to `MTLResourceStorageModeShared` on Apple Silicon UMA; any non-coherent allocation requires `vkInvalidateMappedMemoryRanges` after fence wait.

### 2.2 Damage-Bounded GPU Operations & Avoiding Whole-Frame Readbacks
- **Coalescing Tiny Sparse Regions:** Issuing many 1x1 or tiny sub-rect `VkBufferImageCopy` dispatches under MoltenVK creates per-region `MTLBlitCommandEncoder` command overhead. Coalescing adjacent/overlapping dirty rects or bounding to a single tight damage union (as `VulkanBackend._refresh_host_frame_damage` does when `area * 2 < px_total`) avoids both whole-surface readbacks and excessive blit-command churn.
- **Retained Device Offscreen Surfaces vs Per-Replay Reallocation:** In Simple's `draw_ir_adv.spl`, Vulkan replays intersecting an embedded window surface currently create a brand-new offscreen `VulkanBackend`, render into it, read it back, and shut it down (`5.68-11.6s` on GB10). Caching/reusing a bounded persistent offscreen surface pool (or rendering directly on-device when `opacity_milli == 1000` and clip-bounded, if rounding parity is preserved) removes per-replay device allocation, pipeline creation, and readback overhead while keeping steady-state `present()` free of readback.
- **Device-to-Device Compositing Without Readback:** Per `rendering_ui/skill.md`, production steady-state frames must avoid CPU readback completely (`allocation_count == 0`, `readback_bytes == 0` in timed steady-state), reserving readback strictly for explicit parity/capture harnesses outside timed intervals.
- **MoltenVK Stability:** Multi-frame runs on MoltenVK require strict fence retirement before reusing/destroying command buffers or staging allocations, and avoiding redundant per-frame `clear()` dispatches on unowned/mid-pass buffers (`vulkan_engine2d_sequential_frames_flaky_moltenvk_2026-09-02.md`).

---

## 3. References (via `search_web`)
- Skia analytical path rasterization (`SkScan_AAAPath.cpp`) & `SkRasterPipelineBlitter`: https://skia.googlesource.com / `skia.org`
- Skia `SkCanvas::saveLayer` & `SkBlendMode` Porter-Duff semantics: `skia.org`
- Khronos Vulkan Specification (`vkCmdCopyImageToBuffer`, `VkBufferImageCopy`, pipeline barriers) & MoltenVK Metal blit alignment / storage mode documentation (`vulkan.org`, `khronos.org`, MoltenVK GitHub issues).

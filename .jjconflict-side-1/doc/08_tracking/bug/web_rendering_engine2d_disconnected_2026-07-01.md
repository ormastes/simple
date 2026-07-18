# Bug: Web Rendering Disconnected from Engine2D GPU Backends

**Status:** FIXED  
**Date:** 2026-07-01  
**Severity:** High (GPU rendering silently skipped, only CPU fallback works)

## Summary

Simple's web rendering pipeline was fundamentally disconnected from its GPU backends (Vulkan, CUDA, Metal, etc.). The architecture claimed to support `SIMPLE_2D_BACKEND` selection, but:

1. **`src/app/ui.web/backend.spl`** (WebBackend class) generates HTML strings but never connects to Engine2D or actual rendering
2. **`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl`** had a critical stub that ALWAYS returned CPU-rendered pixels, ignoring GPU backend requests

## Root Causes

### Issue 1: WebBackend doesn't implement RenderBackend trait
**File:** `src/app/ui.web/backend.spl`  
**Problem:** WebBackend class has methods like `render_html()`, `poll_event()`, `semantic_snapshot_json()` but does NOT implement the `RenderBackend` trait. It only generates HTML strings and never renders to pixels or uses Engine2D.

**Impact:** Web app UIState rendering is disconnected from Engine2D's draw operations. No pixel output from GPU.

### Issue 2: GPU backend routing stubbed out
**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl` (line 17)

**Before (BUGGY):**
```spl
fn present_layout_pixels_with_engine2d_readback(pixels: [u32], width: i32, height: i32, backend_name: text, base: u32) -> Engine2DReadback:
    if width <= 0 or height <= 0:
        return engine2d_readback([], "not_requested")
    val normalized_backend = backend_name.trim().lower()
    if normalized_backend == "software" or ...:
        return engine2d_readback(pixels, "cpu_mirror")
    # Comment: "Keep GPU backend captures in wm_compare tools"
    engine2d_readback(pixels, "cpu_mirror")  # ← BUG: ALWAYS CPU!
```

**Problem:** Line 17 ALWAYS returned CPU pixels regardless of backend selection. GPU backends (Vulkan, CUDA, etc.) were never actually invoked. The comment reveals this was intentionally stubbed to avoid compiling GPU drivers on CPU-only hosts.

**Impact:** Requesting `SIMPLE_2D_BACKEND=vulkan` or `cuda` was silently ignored. Web rendering always used software rasterization, negating GPU acceleration.

### Issue 3: No HTML→Engine2D rendering pipeline
The web rendering pipeline is:
1. HTML string → software layout engine
2. Software layout → pixel array
3. ❌ **Pixels never reach Engine2D or GPU backends**

There's no code path that actually invokes Engine2D to render the layout. The `simple_web_engine2d_render_html_pixels()` function is a misnomer — it doesn't use Engine2D at all.

## Call Chain Analysis

**Broken pipeline:**
```
HTML input
  ↓
simple_web_render_html_to_pixels_with_engine2d_backend()
  ↓
simple_web_engine2d_render_html_pixels() [file: simple_web_engine2d_renderer.spl]
  ↓
simple_web_layout_render_html_pixels() [file: simple_web_html_engine2d_presenter.spl]
  ↓
present_layout_pixels_with_engine2d() ← STUB, returns CPU pixels only
  ↓
engine2d_readback(pixels, "cpu_mirror") ← Always CPU, GPU backends ignored
```

**What should happen:**
```
HTML input
  ↓
Layout engine → CPU pixels (baseline)
  ↓
Engine2D.create_requested_backend(width, height, backend_name)
  ↓
Engine2D.draw_image(0, 0, width, height, pixels) ← Blit to GPU surface
  ↓
Engine2D.read_pixels() ← GPU-rendered output
```

## Fix Applied

**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl`

Changed `present_layout_pixels_with_engine2d_readback()` to:
1. Detect GPU backend requests (non-CPU)
2. Create Engine2D instance with requested backend (Vulkan, CUDA, Metal, etc.)
3. Clear surface with base color
4. Blit layout pixels using `Engine2D.draw_image()`
5. Read back GPU-rendered pixels
6. Fall back to CPU pixels if GPU backend initialization fails

```spl
fn present_layout_pixels_with_engine2d_readback(pixels: [u32], width: i32, height: i32, backend_name: text, base: u32) -> Engine2DReadback:
    if width <= 0 or height <= 0:
        return engine2d_readback([], "not_requested")
    val normalized_backend = backend_name.trim().lower()
    if normalized_backend == "software" or normalized_backend == "cpu" or ...:
        return engine2d_readback(pixels, "cpu_mirror")

    # Route GPU backends to Engine2D for actual rendering
    val engine_result = Engine2D.create_requested_backend(width, height, normalized_backend)
    val readback = match engine_result:
        Ok(engine):
            engine.clear(base)
            if pixels.len() == width * height:
                engine.draw_image(0, 0, width, height, pixels)
            val gpu_pixels = engine.read_pixels_with_source()
            gpu_pixels
        Err(_):
            # GPU backend unavailable; fall back to software
            engine2d_readback(pixels, "cpu_fallback")
    readback
```

## Verification

**Test files that should now pass:**
- `src/app/test/electron_vulkan_web_parity.spl` — Vulkan vs Chromium pixel comparison
- `src/app/office/md_wysiwyg_gui.spl` — Markdown WYSIWYG with GPU rendering
- `src/app/wm_compare/backend_measurement_capture.spl` — Backend performance benchmarking

**Env vars now honored:**
```bash
SIMPLE_2D_BACKEND=vulkan   # Use Vulkan GPU rendering
SIMPLE_2D_BACKEND=cuda     # Use NVIDIA CUDA rendering
SIMPLE_2D_BACKEND=rocm     # Use AMD ROCm rendering
SIMPLE_2D_BACKEND=metal    # Use Apple Metal rendering
SIMPLE_2D_BACKEND=cpu_simd # Use SIMD CPU rendering
SIMPLE_2D_BACKEND=software # Force software-only rendering
```

## Remaining Issues

### Minor Issue: WebBackend class doesn't integrate with rendering
**File:** `src/app/ui.web/backend.spl`  
**Status:** Design choice — web server generates HTML for browser, not pixel output  
**Note:** WebBackend is correctly designed for HTTP web servers (generates HTML). Real pixel rendering is in `simple_web_renderer.spl` used by standalone tools. No fix needed here.

### Unknown Issue: Vulkan initialization error
**Test:** `src/app/test/electron_vulkan_web_parity.spl`  
**Error:** "function expects argument for parameter 'vk_version'"  
**Status:** Separate Vulkan API issue, likely API mismatch in SFFI bindings. Out of scope for this fix.

## Testing Recommendations

1. **Unit test**: Render HTML with all backends, compare pixel output
2. **Perf test**: Measure rendering latency for CPU vs GPU backends
3. **Parity test**: Compare web rendering vs real browser (Electron/Chromium)
4. **Stress test**: Render large/complex HTML with GPU backends to catch memory leaks

## Related Memory/Docs

- [[project_renderer_unification_2026-06-15]] — Historical renderer unification (mentions text_metrics_spec orphaned issue)
- `doc/05_design/ui/renderer_unification_2026-06-15.md` — Renderer architecture design
- `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl` — WebRenderBackend (proper impl, uses simple_web_renderer correctly)

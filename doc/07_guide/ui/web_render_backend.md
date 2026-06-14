# Web Render Backend — pure_simple vs chromium

One interface, two interchangeable web-render engines, so the *same* HTML can be
rendered (and compared) by Simple's own renderer or by real Chromium.

- **API:** `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl`
- **Sample app:** `examples/06_io/ui/web_render_backend_gui.spl`
- **Chromium helper:** `tools/web-render-backend/chromium_render.js`
- **WebGPU draw evidence helper:** `tools/web-render-backend/chromium-webgpu-draw/`
- **WebGPU compute evidence helper:** `tools/web-render-backend/chromium-webgpu-compute/`

## The interface

```spl
use std.gc_async_mut.gpu.browser_engine.web_render_backend.{WebRenderBackend}

val r = WebRenderBackend.create("pure_simple", w, h)   # or "chromium"
val pixels = r.render_html_to_pixels(html)             # [u32] 0xAARRGGBB  (comparison)
val opened = r.show_live_window(html_path)             # true for chromium (live window)
```

| backend | display | nature |
|---------|---------|--------|
| `pure_simple` | Engine2D raster frame in a winit window | Simple's HTML layout → Engine2D `auto` (Metal, CUDA/HIP, Vulkan, then CPU fallbacks). No browser. |
| `chromium` | **live, interactive** Electron `BrowserWindow` | real Chromium renders the live DOM. |

`render_html_to_pixels` produces a comparable buffer from **both** engines — this
is what the honest bit-level gate uses (pure-Simple ≡ Chromium OSR, `mismatch=0`).
Pure-Simple pixel artifacts stamp their `engine2d_backend` from the same
Engine2D `auto` resolution path used for rendering; do not hard-code default
artifact provenance as `software`.
The browser backend keeps a retained one-entry pixel artifact cache for
unchanged static full HTML at the same viewport and resolved backend. Requests
with `data-simple-dynamic`, `data-live`, `data-ui-patch`, or WebSocket JS bypass
that retained cache and render directly.
`show_live_window` opens each backend's native window (chromium = live DOM;
pure_simple has no live shell and returns false so the caller presents pixels).

## WebGPU evidence boundary

`WebRenderBackend("chromium")` is not the Chrome WebGPU proof path. It renders
HTML through Electron offscreen and returns comparable pixels for web-renderer
parity. Use `std.gc_async_mut.gpu.browser_engine.chrome_webgpu_draw_evidence`
and `tools/web-render-backend/chromium-webgpu-draw/` when the requirement is
Chrome/Electron WebGPU drawing. That wrapper reports either positive adapter,
non-fallback adapter, device, pipeline, draw, capture, and pixel evidence, or a
deterministic `host-unavailable:*` status without falling back to Simple
software replay. For WASM-originated Simple3D evidence, use
`chrome_webgpu_draw_wasm_simple3d_triangle_payload_evidence`; it parses
`simple3d:canvas:w,h:triangle:x1,y1,z1,x2,y2,z2,x3,y3,z3:rgba:r,g,b,a`,
converts RGB to `#rrggbb`, and records payload byte/checksum provenance even
when the host reports unavailable WebGPU.

For in-process browser Simple-script drawing evidence, use
`canvas_get_context_simple2d` or `canvas_get_context_simple3d` from
`std.gc_async_mut.gpu.browser_engine.script.canvas_api`. Those facades prove the
Simple browser command capture and software-replayed WebGPU submit path. The
Simple3D facade records scene payload bytes/checksum and submission counters; it
does not prove Chrome/Electron hardware-backed WebGPU pixels.

## Running the sample (macOS)

```bash
# pure-Simple raster window (Engine2D auto backend; explicit software remains available)
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_render_backend_gui.spl pure_simple 384x288
# live Chromium window (real DOM, interactive) — viewport arg sets CSS width
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_render_backend_gui.spl chromium 1280x960
```

A `WxH` argv sets the CSS viewport (the page lays out at desktop width so fonts are
proportional); the result is downscaled to the window. A `.html` argv overrides the
page (default: `test/09_baselines/web_html_input/vanillastyle_demo.html`).

## Performance note (pure_simple)

The pure-Simple raster runs interpreted and is canvas-bound. Two O(n²) traps were
fixed (see `doc/08_tracking/bug/pure_simple_web_render_interpreter_bound_2026-06-06.md`):
1. heuristic-surface buffer built with a `push` loop → use `[0; w*h]` array-repeat;
2. the in-place array-write fix (`2d4579a0`) must be in the **running binary** —
   a stale `bin/simple` clones the framebuffer on every pixel write. Keep the
   driver current (rebuild on a stale deploy). Keep pure_simple viewports modest
   (≤ ~400 wide); chromium opens a live window and is unaffected.

## Honest comparison (no memorized pixels)

Use two **independently produced** artifacts + an absolute oracle, never hard-coded
captured pixels. Gate: `scripts/check/check-electron-simple-web-engine2d-bitmap-evidence.shs`
(pure-Simple Engine2D vs real Chromium OSR → `mismatch_count=0`).

For host/GPU lane event-flow and less-ms evidence around
`target.later(...) gpu \:`, use
`doc/09_report/perf/host_gpu_lane_event_flow_perf_evidence_2026-06-14.md`.
That lane records `Engine2dHostGpuEventFlowEvidence`, Draw IR rendered-command
counts, pixel/readback hashes, fallback state, and p50/p95 baseline-vs-candidate
timings. Do not count fallback-only or smoke-size software runs as a real GPU
speedup.

See also: [`web_render_backend_tldr.md`](web_render_backend_tldr.md).

## Chrome WebGPU Evidence Helpers

`std.gc_async_mut.gpu.browser_engine.chrome_webgpu_draw_evidence` is the
canonical host-adaptive draw probe for real Chromium WebGPU pixels.
`std.gc_async_mut.gpu.browser_engine.chrome_webgpu_compute_evidence` is the
matching processing probe for real Chromium WebGPU compute readback. The
compute helper accepts compiler-emitted WGSL through `CWC_WGSL_SOURCE` and can
run both `u32_add` and `simple2d_fill` operations. For WASM-backed Simple2D
processing evidence, use
`chrome_webgpu_compute_wasm_simple2d_fill_payload_bytes_evidence(...)` so the
evidence carries the payload byte count and checksum beside the WGSL source
metadata.

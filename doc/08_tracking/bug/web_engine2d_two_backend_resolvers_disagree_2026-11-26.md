# Browser-engine path resolves the Engine2D backend twice, independently

- **Date:** 2026-11-26
- **Status:** fix-implemented-verification-pending (2026-11-27 W4-5; waiting-for: Linux host 2x discrete NVIDIA GPU `ulimit -n 44` verification)
- **Area:** `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
  (`web_render_resolved_engine2d_backend_name`) and
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`
  (`_resolved_render_backend`)
- **Split out of:** `gpu_probe_then_create_toctou_2026-08-04.md`, section "Separate production
  defect — two independent backend resolvers disagree", which was disclosed there but never filed.

## Defect

The facade and the renderer each call `simple_web_engine2d_resolved_backend_name(...)` on their
own. That function runs a probe, and nothing is cached between the two calls. When the two answers
differ, the facade stamps one backend (for example `vulkan`) and emits a drained queue receipt,
while the renderer rasterises on the CPU and reports `cpu_mirror`. This is the same
resolve-then-use gap as the TOCTOU record, but in production code rather than in a spec.

## Reproduction status

Observed in August under `ulimit -n 44` on a host with 2x discrete NVIDIA GPUs. It did not
reproduce at `ulimit -n 44` on the 2026-11-26 Linux aarch64 GB10 host: 3/3 parity runs reported
`device_readback`, because the fd limit does not disturb that driver. Use
`SIMPLE_2D_PROBE_FAULT=vulkan` to force the divergence.

## Fix direction

Resolve the backend once per render, pass the resolved name or created backend down to the
renderer, and have the facade report what the renderer actually used.

## W4-5 Fix & Windows Verification (2026-11-27)

- **Modified files (browser_engine only; `web_render_pixel_backend.spl` untouched):**
  - `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`: resolve backend once per call via `_simple_web_engine2d_render_html_pixels_resolved`, and cache `resolved_backend` once in `SimpleWebEngine2DStaticPixelCache.create` so `result_for_html` does not re-probe per render miss.
  - `src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`: restore `resolved_backend` on `SimpleWebLayoutEngine2DExecutionResult` and report actual `slot.engine.backend_name()` / `lane_demoted` `"software"` (empty string on invalid/zero viewport) back to callers including `web_render_pixel_backend.spl`.
- **Verified locally (Windows `--mode=interpreter`):**
  - `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine2d_resolver_agreement_spec.spl`: `4/4 PASS` (covers `SIMPLE_2D_PROBE_FAULT=vulkan` parity across facade/renderer, `SIMPLE_2D_CREATE_FAULT=cpu_simd` actual-backend reporting, `SimpleWebEngine2DStaticPixelCache` single-resolve behavior, and zero-size viewport behavior).
  - `test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl`: `4/4 PASS` (GPU branch skipped due to unavailable GPU device on headless Windows).
- **Waiting for:** Live `ulimit -n 44` verification on a Linux host with 2x discrete NVIDIA GPUs.

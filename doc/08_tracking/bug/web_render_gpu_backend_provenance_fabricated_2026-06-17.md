# Web-Render GPU Backend Provenance Fabricated - 2026-06-17

**Status:** fix applied 2026-07-16; executable SPipe verification is blocked
until the pure-Simple test runner is rebuilt. Static rendering and runtime
facade gates pass.

## Severity
P1 — correctness/integrity. Renders false "GPU-backed" provenance into the
shared `WebRenderArtifact` boundary that downstream code and specs trust.

## Component
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl`
- `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
- Spec asserting the lie: `test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl`

## Summary
The web-render pixel path stamps `WebRenderArtifact.engine2d_backend` (and the
host/GPU runtime-queue provenance fields: `queue_backend_handle == 7`,
`queue_packet_id == 1`, `queue_drained == 1`, payload `backend=vulkan`) from the
**requested backend name**, not from the backend that actually produced the
pixels. The pixel producer never touches a GPU backend at all.

## Root Cause
1. `simple_web_engine2d_render_html_pixels(html, w, h, backend_name)`
   (`simple_web_engine2d_renderer.spl:817`) is a **pure-CPU HTML heuristic
   rasterizer**. It inspects HTML strings (`_html_background_color`,
   `_first_block_color`, `contains(...)`) and paints pixels in pure Simple. The
   `backend_name` argument is only threaded through as a label — the function
   never constructs `VulkanBackend`, never calls any `rt_vulkan_*`, and never
   routes through `Engine2D.create_requested_backend`. The local `engine`
   object it uses for generated-widget HTML (lines 27-40) is a CPU
   mini-rasterizer defined in the same file, not the Engine2D/VulkanBackend GPU
   path.
2. `simple_web_engine2d_resolved_backend_name(w, h, backend_name)` (line 1084)
   returns the requested name verbatim for `vulkan`/`metal`/`directx`/`cuda`/...
   **with no availability check** (only `"auto"` probes via
   `Engine2D.detect_best_backend()`).
3. `web_render_artifact_with_runtime_queue_evidence`
   (`web_render_pixel_backend.spl:86`) then synthesizes "submitted/drained"
   queue provenance with a fixed `backend_handle == 7` whenever the *label* is a
   GPU backend, via the pure-Simple `engine2d_host_gpu_*` state-machine
   simulation — independent of any real GPU submission.

Net effect: requesting `backend="vulkan"` yields an artifact stamped
`engine2d_backend == "vulkan"` with GPU-queue provenance, while the pixels were
CPU-rasterized — **even on a host where Vulkan is fully available**. The label
describes a request, not a fact.

## Evidence
- Read of `simple_web_engine2d_render_html_pixels` / `_readback`: no GPU call
  sites; `backend_name` is passthrough-only.
- `Engine2D.create_requested_backend(w, h, "vulkan")` (engine.spl:140) is the
  *correct* pattern by contrast: it constructs `VulkanBackend`, calls `init()`,
  returns the vulkan-backed engine only on success, falls back to CPU otherwise,
  and sets `selected_backend_name` to the **actual** backend. The web path
  bypasses this entirely.
- `web_render_pixel_backend_queue_spec.spl` asserts `engine2d_backend ==
  "vulkan"` and `queue_backend_handle == 7`. Because (1)–(3) above, that spec is
  asserting the fabricated provenance — it is part of the bug, not a guard
  against it.

## Honest Reference (added this session)
`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`
drives the *real* `VulkanBackend` (real `spirv_clear` + `spirv_rect_filled`
compute dispatch, device readback) and verifies every pixel against a pure-Simple
CPU oracle (0 mismatches over a 16x8 framebuffer under `bin/simple test`). This
shows the real GPU path works and is verifiable — the web path simply does not
use it.

## Implemented Fix

- Deleted the fixed backend handle `7` and passes only the handle returned by
  `Engine2DReadback` / `Engine2dDrawIrAdvResult`.
- Runtime queue emission now requires `device_readback` and a positive handle,
  submits the artifact checksum and payload text, and stamps evidence only when
  the drained handle, byte count, checksum, and payload text all match.
- CPU mirrors and cache hits are labeled `software`, stay queue-neutral, and
  use the explicit reason `cached Engine2D pixel mirror`.
- The focused spec accepts a GPU row only when the live readback supplies the
  device source and handle; a host without that device proves fail-closed
  neutrality only, not positive GPU execution.

The larger renderer-routing work remains separate: production acceptance still
requires retained live device readback and matching pixels from the canonical
GPU gate.

## Related
- `rt_vulkan_only_executes_under_classic_interpret_2026-06-17.md` (why GPU
  backends silently no-op outside the classic interpreter).

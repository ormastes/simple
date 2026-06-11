# GUI/Backend Performance Agent Task Plan

Lane: ongoing Simple GUI/backend performance convergence
Updated: 2026-06-11

## Completed (already pushed)

- `2dc841a399` -- font offload backend selection: added
  `engine2d_font_offload_backend_order()` and
  `engine2d_backend_lane_preferred_font_offload_candidate(...)` so vector and
  bitmap font offload use a stable processing-lane order: Metal, CUDA, ROCm/HIP,
  Qualcomm, Vulkan, DirectX, OpenCL, OpenGL, Intel, WebGPU, CPU SIMD, software,
  then CPU. Evidence: `backend_lane_spec.spl` now covers alias handling and
  native GPU lanes before Vulkan.
- this commit -- preferred font offload evidence wrappers: added vector and
  bitmap evidence helpers that apply the Engine2D font offload order to probed
  backend candidates before building typed evidence. Evidence:
  `vector_font_offload_spec.spl` and `bitmap_font_offload_spec.spl` cover ROCm
  alias selection before Vulkan and explicit CPU fallback behavior.
- this slice -- preferred font readback evidence wrappers: added
  `vector_font_preferred_glyph_readback_evidence(...)` and
  `bitmap_glyph_raster_preferred_mask_readback_evidence(...)` so glyph readback
  evidence now applies Engine2D font offload lane preference before submit/readback
  classification.
- `275a221f5d` -- production GUI web parity render path: replaced O(n^2)
  distinct-color scan with dictionary membership, reused deterministic parity
  reports, skipped Metal fallback rerender/compare on software hosts, and added
  a scoped fast path for the production parity common.ui widget fixture. Evidence:
  `production_gui_web_renderer_parity_hardening_spec.spl` improved from a 120s
  timeout to 8 passing examples in 6.6s.
- this commit -- production GUI render timing evidence: `ProductionGuiWebParityReport`
  and `BackendExecutedGuiSceneReport` now carry per-backend render elapsed
  microseconds plus total elapsed time. Evidence:
  `production_gui_web_renderer_parity_hardening_spec.spl` asserts timing fields,
  and `check-production-gui-web-backend-executed-evidence.shs` writes the timing
  values into backend evidence reports.
- this commit -- render timing budget classification: production GUI parity
  reports now include timing budget, status, and reason fields for generated
  widget rendering and backend-executed Engine2D rendering. Evidence:
  `production_gui_web_renderer_parity_hardening_spec.spl` asserts focused paths
  remain within budget, and the backend evidence wrapper emits the budget fields.
- this commit -- render throughput evidence: production GUI parity reports now
  derive per-backend and total pixels-per-second from pixel counts and measured
  elapsed time. Evidence: `production_gui_web_renderer_parity_hardening_spec.spl`
  asserts positive throughput, and the backend evidence wrapper emits throughput
  fields for software, CPU SIMD, Metal, and total render paths.
- `e0a0ec15f0c60d96dd320054e02c8309229e54ce` -- `perf(gui): carry browser text line widths`
- `248bf87` -- glyph fallback scan removal
- `c166d` -- backend preference lanes
- `97ed` -- DirectX backend order

## Current remaining work

1. Collect and record additional startup/render evidence (timing + throughput + parity)
   - Run and archive the full production GUI web renderer parity evidence wrapper with
     the new timing and throughput fields.
   - Add broader throughput thresholds after enough host-stable samples exist.
2. Provide GPU/font offload proof
   - Demonstrate measured proof of real GPU/font offload path behavior or explicit typed unavailability.
   - Ensure device submit/readback evidence uses preferred glyph readback wrappers after
     candidate ordering.
3. Execute focused pure Simple GUI text/layout optimization pass
   - Target isolated hot-path opportunities in text layout, line width handling, and browser text path.
   - Keep changes small and attributable with before/after measurements.
4. Preserve app behavior
   - Keep rendering semantics and UI behavior unchanged while tuning performance.
   - Add or refresh regression checks if behavior drift risk is introduced by any micro-optimization.

## Near-term handoff priorities

- Update backend startup/render evidence set first.
- Capture GPU/font offload decision proofs second.
- Continue pure Simple text/layout optimization with explicit behavior-preservation checks.

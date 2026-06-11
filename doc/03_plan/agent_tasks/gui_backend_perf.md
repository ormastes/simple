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
- this commit -- backend render sample aggregation: the backend-executed evidence
  wrapper now runs three reduced-scene samples and emits min/avg/max total
  elapsed time plus min/avg/max total throughput. Evidence:
  `check-production-gui-web-backend-executed-evidence.shs` fails if any sample
  loses exact parity, CPU SIMD execution, Metal readback requirements, or timing
  budget status.
- this commit -- top-level parity sample propagation: the canonical production
  GUI web renderer parity wrapper now promotes backend sample count plus
  min/avg/max elapsed and throughput into
  `production_gui_web_renderer_parity_backend_*` fields and its Markdown
  summary, so archived full-wrapper reports retain the aggregate evidence.
- this commit -- production GUI font offload evidence: added
  `scripts/check/check-production-gui-font-offload-evidence.shs` to exercise the
  preferred vector and bitmap font offload/readback wrappers together and emit
  explicit typed unavailable rows when the host has no device submit/readback
  proof.
- this commit -- top-level font evidence propagation: the canonical production
  GUI web renderer parity wrapper now runs the font offload/readback wrapper and
  promotes typed vector and bitmap font evidence under
  `production_gui_web_renderer_parity_font_offload_*` fields.
- this commit -- Chrome live capture timeout hardening: the Chrome layout
  bitmap evidence wrapper now bounds DevTools capture with
  `CHROME_LAYOUT_TIMEOUT_SECS` / `CHROME_LAYOUT_KILL_SECS`, emits
  `chrome-live-capture-timeout`, and cleans up spawned Chrome children on
  signal/exit so full parity evidence cannot hang indefinitely in the surface
  manifest.
- this commit -- surface manifest tracked-text policy: the Tauri/Chrome surface
  manifest now preserves exact-pixel requirements for text-free rows while
  counting `policy=track-text-divergence` rows separately as tracked evidence.
  Top-level production parity accepts exact+tracked coverage only when exact
  rows have zero mismatches and tracked rows keep `blur_or_tolerance=false`.
- this commit -- scaled glyph hot-path dispatch removal: the Simple Web HTML
  layout renderer no longer calls an always-true sparse-hit helper for every
  scaled glyph pixel. Scaled glyphs still render solid, preserving the prior
  visual semantics while removing per-pixel function dispatch from GUI text
  startup rendering.
- this commit -- flex stretch style-copy optimization: `styles_with_height`
  now preallocates the output style array and assigns by index instead of
  rebuilding it through repeated single-element appends. This removes a
  quadratic copy pattern from flex stretch layout while preserving the returned
  style values.
- this commit -- Engine2D selector verification unblock: the heuristic
  Engine2D renderer now uses a token-exact local class matcher for the
  `:has(> .badge)` fast path instead of calling a missing `class_has` helper.
  This restores the focused Engine2D renderer spec as usable regression
  coverage for later startup/render optimizations.
- this commit -- RGB token allocation removal: `_css_rgb_color` now parses the
  first three RGB components into scalar slots instead of pushing each token
  into a temporary array. This removes per-call dynamic array allocation/copy
  work from CSS color parsing in the heuristic Engine2D startup path.
- this commit -- Engine2D loop length hoisting: the heuristic surface clear
  loop, first-class lookup, selector rule scan, and style-block selector scan
  now hoist stable `.len()` values out of loop conditions. This trims repeated
  dispatch in GUI startup scanning and pixel-fill hot paths without changing
  rendered output.
- this commit -- CSS scan length hoisting: `_find_char_from`,
  `_last_hex_color_after`, `_resolve_current_color`,
  `_declaration_background_color`, and the `:not(...)` class scan now reuse
  stable string/list lengths inside their loops. This trims repeated length
  dispatch in color and selector parsing used by the heuristic Engine2D startup
  path.
- `e0a0ec15f0c60d96dd320054e02c8309229e54ce` -- `perf(gui): carry browser text line widths`
- `248bf87` -- glyph fallback scan removal
- `c166d` -- backend preference lanes
- `97ed` -- DirectX backend order

## Current remaining work

1. Collect and record additional startup/render evidence (timing + throughput + parity)
   - Run and archive the full production GUI web renderer parity evidence wrapper
     now that it promotes backend aggregate sample fields.
   - Current local blocker after installing `tools/electron-shell` dependencies:
     generated-GUI Electron matrix and layout manifest pass, but the
     Tauri/Chrome surface manifest still fails with live-surface divergence
     (`tauri`: 16/18 pass, 216 mismatches; `chrome`: 14/18 pass, 1785 mismatches
     in the latest local run) and one bounded Chrome timeout row.
   - Re-run the surface manifest after the tracked-text policy change; any
     remaining failures should now represent exact-row divergence or a bounded
     host capture timeout, not the two known text-raster tracking rows.
   - Add broader throughput thresholds after enough host-stable samples exist.
2. Provide GPU/font offload proof
   - Demonstrate measured proof of real vector/bitmap GPU font offload and readback path behavior or explicit typed unavailability.
   - Use `scripts/check/check-production-gui-font-offload-evidence.shs` as the
     canonical evidence wrapper for current host captures.
   - Use `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`
     for archived production GUI parity captures; it promotes the font evidence
     into its top-level report.
   - Ensure device submit/readback evidence uses preferred glyph readback wrappers after
     candidate ordering.
   - For every relevant wrapper execution, capture `status_code` plus `reason`:
     vector statuses include `gpu-glyph-returned`,
     `gpu-proof-with-cpu-glyph`, `cpu-fallback`,
     `vector-font-glyph-readback-matched`,
     `vector-font-glyph-not-submitted`, `vector-font-glyph-return-missing`,
     and `cuda-runtime-unavailable`; bitmap statuses include
     `gpu-copy-with-cpu-glyph`, `cpu-glyph-baseline`,
     `gpu-glyph-raster-readback-matched`, `gpu-glyph-raster-not-submitted`,
     `gpu-glyph-raster-invalid-expected-checksum`, and
     `opencl-runtime-or-queue-unavailable`.
   - Prefer explicit unavailable status/reason rows over silent fallback for
     missing runtimes, queues, or readback.
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

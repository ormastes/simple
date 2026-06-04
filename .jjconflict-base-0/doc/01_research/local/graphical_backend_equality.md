<!-- codex-research -->
# Graphical Backend Equality — Local Research

Date: 2026-06-03

## Objective

Research how to improve graphical/backend equality tests by adding a common
test interface, multiple backend support, normalized captures, and equivalent
drawing cases across 2D, web, GUI, and WM paths.

## Existing Repo Surfaces

- `doc/01_research/local/shared_wm_renderer_unification.md` and
  `doc/03_plan/shared_wm_renderer_unification_completion_audit.md` show the
  shared Web/Electron/Tauri/pure Simple API, CPU/Metal/CUDA Engine2D interface,
  and host/SimpleOS WM logic sharing are considered complete for their current
  contract.
- `test/03_system/wm_compare/backend_measurement_capture_spec.spl` and
  `src/app/wm_compare/backend_measurement_capture.spl` already capture backend
  timing/RSS/binary-size evidence and build a Metal/Vulkan/CUDA/CPU SIMD matrix
  with explicit unavailable GPU lanes.
- `src/app/wm_compare/backend_measurement_report.spl` validates initialized
  acceleration lanes, rejects fallback for acceleration lanes, and serializes
  SDN measurement records.
- `test/03_system/wm_compare/comparison_failure_report_spec.spl` already separates
  capture failure, metadata mismatch, structural/layout mismatch, exact pixel
  mismatch, and backend unavailability.
- `test/02_integration/rendering/backend_screenshot_compare_spec.spl` and
  `test/02_integration/rendering/screenshot_compare_helpers.spl` already cover
  deterministic exact software/CPU buffers, thresholded GPU-like buffers, and
  diff-image generation through `os.compositor.screenshot_compare`.
- `src/lib/gc_async_mut/gpu/engine2d/backend.spl` is the current core 2D
  interface with draw operations, `present()`, `read_pixels()`, `width()`, and
  `height()`. `src/lib/gc_async_mut/gpu/engine2d/engine.spl` exposes strict
  backend creation, backend listing, backend naming, and readback.
- `src/lib/gc_async_mut/gpu/engine2d/backend_session.spl` contains backend
  session and policy metadata that can feed availability reporting, but should
  not become the equality interface itself.
- `src/os/compositor/tolerance_profile.spl` already has strict, text, glass,
  and window-manager tolerance profiles that should be reused before creating a
  new tolerance vocabulary.
- `doc/03_plan/sys_test/production_gui_web_renderer_parity_hardening.md`
  records live Electron generated-GUI evidence with exact pixel divergence and
  artifact paths. This proves the live capture path exists but not equality.
- `doc/03_plan/gui_hardening_current_plan_2026-06-01.md` already uses frequent
  `jj git fetch` checkpoints and records when no rebase/push is attempted due
  to dirty or detached working-copy state.

## Gap Analysis

The repo has backend-specific comparison pieces, but it does not yet have one
first-class graphical equality contract that can say:

- this shared scene/drawing case was rendered by these requested backends;
- these are the logical size, physical size, scale factor, panel/content/window
  rectangles, color space, and capture kind;
- these backends produced equivalent drawings under exact, strict GPU, or
  native-chrome policy;
- these artifacts explain the failure without relying on a single raw pixel
  mismatch count.

Additional render-side gaps from the parallel explorer:

- `test/02_integration/rendering/screenshot_compare_helpers.spl` references
  `std.gc_async_mut.gpu.browser_engine.backend_screenshot_capture.BackendCapture`,
  but that module is missing, so the helper is not a complete real-backend
  capture harness.
- `test/02_integration/rendering/backend_screenshot_compare_spec.spl` validates
  comparison behavior with fixture buffers, not real Engine2D captures.
- `test/02_integration/rendering/engine2d_cpu_vulkan_parity_spec.spl` is named as
  CPU/Vulkan parity, but its current real comparison coverage is CPU/software;
  Vulkan object creation is checked without real Vulkan pixel comparison.
- `test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl` is currently
  the strongest real backend parity runner and should be used as the model for
  false-green guards.

The next refactor should not replace the completed shared-WM renderer API. It
should add a test-facing adapter above existing pieces:

- `RenderCase`: canonical scene/case data for rectangles, rounded rectangles,
  paths, text metadata, images, clips, transforms, and layers.
- `GraphicalBackendSpec`: URI-like backend selector such as `2d:cpu`,
  `2d:vulkan`, `web:simple`, `gui:electron`, or `wm:host`.
- `GraphicalCapture`: normalized RGBA pixels plus required geometry metadata.
- `GraphicalEqualityReport`: metadata result, shape result, color result,
  backend capability/result, and artifact paths.

## Best Extension Points

- Add app/test-facing equality modules near `src/app/wm_compare/` first because
  this lane already owns capture reports, backend measurement evidence, and
  failure classification.
- Reuse `os.compositor.screenshot_compare` for the first exact/threshold pixel
  layer instead of inventing a new diff engine immediately.
- Add an Engine2D capture wrapper around `RenderBackend`/`Engine2D` readback
  before migrating render tests to the common contract.
- Extend `test/03_system/wm_compare/` with system-level contract specs after
  requirements are selected.
- Keep engine2d backend conformance under existing rendering specs and connect
  it through the same `GraphicalBackendSpec` vocabulary.

## GitHub Sync Note

`jj git fetch` was run on 2026-06-03 and reported `Nothing changed`. The
worktree has unrelated dirty files, so the plan should require fetch checkpoints
before and after each agent integration, but avoid rebase or push until the lane
is clean and the user approves.

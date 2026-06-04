# Graphical Backend Equality — Agent Task Plan

Date: 2026-06-03

## Coordination Rules

- Agents must use disjoint write scopes.
- Agents must not revert unrelated dirty files.
- The lead runs `jj git fetch` before integrating each returned patch.
- No final requirements or implementation should begin until the user selects
  feature and NFR options.

## Proposed Parallel Agents

1. Render parity agent
   - Scope: `test/02_integration/rendering/`, `src/os/compositor/screenshot_compare.spl`,
     and rendering guide docs.
   - Task: map existing exact/threshold helpers into the future
     `RenderCase`/`GraphicalEqualityReport` contract, repair the missing
     backend capture wrapper, and avoid treating fixture-buffer checks as real
     backend parity.

2. WM/web capture agent
   - Scope: `src/app/wm_compare/`, `test/03_system/wm_compare/`, Electron evidence
     scripts, and `doc/09_report` GUI parity reports.
   - Task: add normalized capture metadata and failure-report scenarios.

3. Backend selector agent
   - Scope: new selector/model files only after requirements are selected.
   - Task: parse backend specs such as `2d:cpu`, `2d:vulkan`, `web:simple`,
     `gui:electron`, and `wm:host`; expose capability and unavailable status.

4. Manual/spec agent
   - Scope: SPipe specs and generated/manual docs only.
   - Task: keep executable specs real, regenerate `doc/06_spec`, and review the
     generated scenario manual for usability.

## Sync Cadence

- Start: `jj git fetch`.
- After each agent result: `jj git fetch`, inspect `jj status`, then integrate.
- Before verify: `jj git fetch`; rebase only if clean enough and approved.
- Before release handoff: verify must show PASS; push remains user-approved.

## First Safe Slice

Implement only the common model and specs for metadata/equality classification,
then migrate one WM comparison fixture. Do not touch native GPU kernels or
production renderer hot paths in the first slice.

## Known Render-Side Gaps To Assign

- Replace or repair the missing
  `std.gc_async_mut.gpu.browser_engine.backend_screenshot_capture.BackendCapture`
  dependency in `test/02_integration/rendering/screenshot_compare_helpers.spl`.
- Do not claim Vulkan parity from
  `test/02_integration/rendering/engine2d_cpu_vulkan_parity_spec.spl` until real
  Vulkan pixels are compared against CPU/software readback.
- Use `test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl` as the
  model for false-green prevention in real backend equality tests.

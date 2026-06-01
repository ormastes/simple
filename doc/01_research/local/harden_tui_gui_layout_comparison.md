<!-- codex-research -->
# Local Research: Harden TUI/GUI Layout Comparison

Date: 2026-06-01

## Scope

Research for hardening TUI and GUI layout comparison, fixing reachable comparison defects, and planning size/performance evidence across Metal, Vulkan, CUDA, and SIMD CPU paths.

## Current Comparison And Capture Paths

- `src/app/wm_compare/main.spl` is the unified pixel capture/compare orchestrator. Its documented model is Electron baseline, live host Simple Web WM, and QEMU Simple OS self-rendering, with memcmp-first comparison and tolerance fallback.
- `src/app/wm_compare/html_compat.spl` delegates Chrome/Simple HTML compatibility work to split modules and writes Chrome, Simple, diff, and report artifacts under `test/baselines/html_compat`.
- `src/app/wm_compare/emulated_capture.spl` provides deterministic in-process capture over Simple Web Renderer and Engine2D software. It exposes `capture_simple_web_emulated`, `capture_engine2d_software_emulated`, and `compare_emulated_screenshots_exact`.
- `src/app/wm_compare/site_corpus_layout_report.spl` compares Simple text layout lines against captured Chrome metrics for famous-site corpus samples, tracks missing metrics, mismatches, and first missing line.
- `src/os/compositor/screenshot_compare.spl` is the shared pixel compare utility with `compare_pixel_buffers`, `compare_exact`, `compare_with_profile`, and `generate_diff_image`.

## TUI And GUI Layout Surfaces

- TUI surfaces are spread across `src/app/editor/tui_shell*.spl`, `src/app/llm_dashboard/tui/`, `src/app/ui.render/tui_widgets*.spl`, and `src/lib/*/tui/layout.spl`.
- GUI/layout surfaces include `src/app/editor/gui_shell*.spl`, `src/app/ui.render/layout.spl`, `src/lib/common/ui/layout.spl`, `src/lib/editor/view/layout.spl`, and `src/lib/gc_async_mut/gpu/browser_engine/layout*.spl`.
- Existing system specs include `test/system/gui/tui_screen_spec.spl`, `test/system/gui/glass_pixel_compare_spec.spl`, `test/system/wm_compare/emulated_capture_spec.spl`, and `test/integration/rendering/backend_screenshot_compare_spec.spl`.

## Performance And Backend Surfaces

- Engine2D backend files exist for `backend_metal.spl`, `backend_vulkan.spl`, `backend_cuda.spl`, `simd_kernels.spl`, `simd_provider.spl`, and session wrappers in `src/lib/gc_async_mut/gpu/engine2d/`.
- Sync/no-GC mirrors exist for CUDA, Vulkan, Metal, and SIMD session paths under `src/lib/nogc_sync_mut/gpu/engine2d/`.
- Prior docs already record GPU backend gaps: Metal may be present in source but not wired as verified runtime evidence on macOS ARM64; CUDA is unavailable on Apple Silicon; Vulkan evidence is host/target-specific and cannot prove macOS GUI behavior.
- Existing size/perf work includes `doc/01_research/local/pure_simple_profile_guided_executable_optimization_2026-06-01.md`, `doc/03_plan/render_2d_optimization_plan_2026-05-30.md`, and `doc/08_tracking/perf/graphics_2d_macos_arm64_2026-05-16.md`.

## Defect Candidates

- `src/os/compositor/screenshot_compare.spl`: `compare_pixel_buffers` counts pixels within threshold as matching but still sets `passed` to `diff_count == 0`. Thresholded comparisons therefore report useful match percentages but do not make `passed` reflect threshold acceptance unless routed through `compare_with_profile`.
- `src/app/wm_compare/emulated_capture.spl`: `compare_emulated_screenshots_exact` compares pixel arrays even if either capture result failed, which can collapse capture failure into a generic mismatch instead of a capture error.
- `test/system/gui/tui_screen_spec.spl`: parse-error branches use `expect(false).to_equal(true)`, which loses the parse error and is a placeholder-like failure shape verify should reject.
- `doc/09_report/qemu_gtk_wm_capture_evidence_2026-06-01.md` records qemu-side perf status as failed because the contract program failed, so it is not valid performance evidence.
- `doc/08_tracking/bug/wm_compare_system_specs_visible_failures.md` exists and should be used as prior bug context before claiming wm_compare system specs are hardened.

## Existing Evidence Commands

- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/glass_pixel_compare_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

## Baseline Evidence: 2026-06-01

- `bin/simple test ...` is not the valid test runner in this checkout because `bin/simple` is currently the bootstrap compiler wrapper and returns `unknown command 'test'`. `src/compiler_rust/target/debug/simple` and `bin/simple-interp` expose the test command.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter` passed: 1 file, 3 tests, about 55.7 seconds.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter` passed: 1 file, 11 tests, about 5.3 seconds.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter` failed: 1 file failed, 0 passed, about 2.5 seconds. JSON output reports file failure with `error: null`.
- The failing backend screenshot spec imports `std.gc_async_mut.gpu.browser_engine.backend_screenshot_capture` and `print_comparison_report`, `compare_with_tolerance`, `print_multi_backend_report`, and `BackendCompareEntry` from `os.compositor.screenshot_compare`, but current source search did not find those definitions. This points to stale test/API drift, not a validated backend mismatch.
- `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`, so the doc/spec layout gate is currently clean.

## Baseline Evidence Update: 2026-06-01

- `test/integration/rendering/backend_screenshot_compare_spec.spl` and its `.spipe_matchers_...` mirror were updated to remove dead imports and exercise deterministic screenshot comparison buffers directly. The spec no longer imports the stale `backend_screenshot_capture` module or missing `screenshot_compare` report helpers.
- The updated backend screenshot comparison spec passed under `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`: 1 file, 6 tests, 0 failures. The runner reported the unchanged cached result with slowest prior execution at about 2.0 seconds.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter` still passed: 1 file, 3 tests, about 57.6 seconds.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter` still passed: 1 file, 11 tests, about 5.2 seconds.
- While adapting the stale spec, importing the current Engine2D backend stack exposed a separate backend-session API drift: `BackendSessionKind.CpuSimd` is referenced through the GPU stack while the compiler resolves a shape without that field. That issue is relevant to the requested SIMD CPU backend lane and should be designed as a backend API hardening item rather than hidden inside a screenshot comparison utility test. Tracked in `doc/08_tracking/bug/backend_session_kind_cpu_simd_api_drift_2026-06-01.md`.

## Implementation Evidence Update: 2026-06-01

- `src/os/compositor/screenshot_compare.spl` now separates exact equality from threshold acceptance. `exact_match` is true only when source pixels are byte-for-byte equal; `passed` is true when no pixel exceeds the supplied threshold.
- `test/integration/rendering/backend_screenshot_compare_spec.spl` now asserts thresholded near-channel differences are not exact but still pass tolerance. This closes the earlier ambiguity where thresholded comparisons could be reported as exact.
- Focused verification after the comparison contract fix:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`: 1 file, 6 tests, 0 failures, about 2.1 seconds.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter`: 1 file, 3 tests, 0 failures, about 4.3 seconds.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter`: 1 file, 11 tests, 0 failures, about 5.1 seconds.
  - `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.

## TUI Spec Hardening Update: 2026-06-01

- `test/system/gui/tui_screen_spec.spl` no longer uses placeholder-style `expect(false).to_equal(true)` branches for parse failures. The `Err(e)` branches now assert `e == ""`, which keeps the test failing if parsing regresses while preserving the parser diagnostic in the assertion value.
- Placeholder scan after the edit found no `expect(false).to_equal(true)`, `expect false == true`, `pass_todo`, `TODO`, or `FIXME` markers in `test/system/gui/tui_screen_spec.spl`.
- Focused verification after the TUI spec hardening:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter`: 1 file, 11 tests, 0 failures, about 5.4 seconds.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`: 1 file, 6 tests, 0 failures (cached unchanged result).
  - `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.

## TUI Scenario Manual Update: 2026-06-01

- Regenerated `doc/06_spec/system/gui/tui_screen_spec.md` from `test/system/gui/tui_screen_spec.spl` with `src/compiler_rust/target/debug/simple spipe-docgen ... --output doc/06_spec`.
- The regenerated manual includes the two parser diagnostic assertions for `minimal.ui.sdn` and `demo.ui.sdn`.
- Added a manual-purpose section describing the screen-buffer contract, parser diagnostic behavior, and operator-visible TUI layout outcomes.
- Post-manual verification:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter`: 1 file, 11 tests, 0 failures, about 5.3 seconds.
  - `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.

## Focused Verify-Blocker Audit: 2026-06-01

- Scanned changed comparison/TUI artifacts for `pass_todo`, placeholder
  true/false assertions, `TODO`, `FIXME`, `placeholder`, `stub`, and `dummy`.
  Matches were documentation references to removed issues, not live blockers in
  changed executable specs or source.
- Confirmed manual mirrors exist for changed specs:
  - `doc/06_spec/integration/rendering/backend_screenshot_compare_spec.md`
  - `doc/06_spec/system/gui/tui_screen_spec.md`
- Focused audit commands:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`: 1 file, 6 tests, 0 failures.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter`: 1 file, 11 tests, 0 failures.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter`: 1 file, 3 tests, 0 failures, about 58.7 seconds.
  - `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.

## Scenario Manual Update: 2026-06-01

- Regenerated `doc/06_spec/integration/rendering/backend_screenshot_compare_spec.md` from `test/integration/rendering/backend_screenshot_compare_spec.spl` with `src/compiler_rust/target/debug/simple spipe-docgen ... --output doc/06_spec`.
- Docgen completed successfully but classified the generated content as a stub, so the markdown mirror now includes a manual-purpose section explaining the deterministic-buffer contract, threshold semantics, and why hardware-backed Metal/Vulkan/CUDA/SIMD evidence belongs in backend-qualified specs.
- The manual lists all 6 backend screenshot comparison scenarios and keeps executable SPipe folded under each scenario.
- Post-manual verification:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`: 1 file, 6 tests, 0 failures (cached unchanged result).
  - `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.

## Fixture Size Performance Update: 2026-06-01

- `test/system/wm_compare/emulated_capture_spec.spl` first scenario only asserts that Simple Web Renderer returns a screenshot-shaped pixel buffer with the requested dimensions. It does not need the earlier 160x120 fixture to cover that contract.
- Reduced that shape-only fixture to 40x30 in both the executable spec and `test/sys/wm_compare/.spipe_matchers_emulated_capture_spec.spl`, matching the other emulated capture scenarios.
- Focused verification after the size reduction:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter`: 1 file, 3 tests, 0 failures; runner duration 7899ms; wall time 46.5s. Previous focused verify-blocker audit measured the same spec at about 58.7s runner duration.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`: 1 file, 6 tests, 0 failures; cached unchanged result.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter`: 1 file, 11 tests, 0 failures; runner duration 5486ms.

## Emulated Capture Failure-Triage Update: 2026-06-01

- `src/app/wm_compare/emulated_capture.spl` now rejects invalid viewport dimensions before invoking either renderer. This prevents zero-size or negative-size requests from producing empty successful captures.
- `compare_emulated_screenshots_exact` now returns a non-exact failure result when either capture fails, preventing two empty failed buffers from being reported as an exact match.
- `test/system/wm_compare/emulated_capture_spec.spl` now covers both invalid capture rejection and failed-capture comparison triage. The matcher mirror was updated with the same scenarios.
- `doc/06_spec/system/wm_compare/emulated_capture_spec.md` was updated manually with the new scenarios. Automatic docgen was attempted by the test runner but is currently blocked by unrelated dirty-worktree compiler parse state: `src/compiler/10.frontend/flat_ast_bridge_part2.spl` reports `Unexpected token: expected expression, found Else`.
- Focused verification:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter`: 1 file, 5 tests, 0 failures; runner duration 7346ms.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`: 1 file, 6 tests, 0 failures; cached unchanged result.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter`: 1 file, 11 tests, 0 failures; runner duration 5294ms.
  - `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.

## Shared Exact-Comparison Contract Update: 2026-06-01

- `src/app/wm_compare/html_compat_part1.spl` shared `compare_exact` could previously return `different_pixels == 0` for invalid zero-size comparisons because `total == 0` skipped the pixel loop and produced a zero-difference result. Several callers derive exactness from `different_pixels == 0`.
- `compare_exact` now treats `width <= 0` or `height <= 0` as a non-exact comparison with `different_pixels: 1`, `match_percentage: 0`, and `max_channel_diff: 255`.
- `test/system/wm_compare/html_compat_spec.spl` now covers invalid dimensions in the bitwise pixel comparison context.
- Focused verification:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/html_compat_spec.spl --mode=interpreter`: 1 file, 14 tests, 0 failures; runner duration 8762ms.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter`: 1 file, 5 tests, 0 failures; runner duration 7756ms.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`: 1 file, 6 tests, 0 failures; cached unchanged result.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter`: 1 file, 11 tests, 0 failures; runner duration 5579ms.
  - `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.
  - Placeholder scan over changed comparison/TUI executable artifacts found no live `pass_todo`, false-pass assertions, `TODO`, or `FIXME` markers.

## Backend Runtime Evidence Update: 2026-06-01

- Rechecked the recorded CPU SIMD backend-session API drift. Clean targeted checks pass for `backend_session_contract_spec.spl`, `cpu_simd_session_contract_spec.spl`, `gc_async_mut/gpu/engine2d/backend_session.spl`, `nogc_sync_mut/gpu/engine2d/backend_session.spl`, and `gc_async_mut/gpu/engine2d/engine2d_api.spl`; the original `BackendSessionKind.CpuSimd` field error is not currently reproducible.
- `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl` `probe_runtime_evidence_summary` now evaluates Metal and Vulkan before CUDA/compute-only fallbacks when choosing selected runtime evidence. The summary now also exposes `metal_status`, `vulkan_status`, `cuda_status`, `cpu_simd_x86_status`, `cpu_simd_arm_status`, and `cpu_simd_riscv_status`.
- `test/unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` now asserts these explicit backend status fields are present in the runtime evidence summary.
- Focused verification:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/gpu/engine2d/backend_probe_strict_spec.spl --mode=interpreter --clean`: 1 file, 8 tests, 0 failures; runner duration 1409ms.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/gpu/engine2d/backend_session_contract_spec.spl --mode=interpreter --clean`: 1 file, 3 tests, 0 failures; runner duration 120ms.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl --mode=interpreter --clean`: 1 file, 3 tests, 0 failures; runner duration 709ms.
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/html_compat_spec.spl --mode=interpreter`: 1 file, 14 tests, 0 failures; runner duration 8412ms.
  - `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.
  - Placeholder scan over changed backend/comparison executable artifacts found no live `pass_todo`, false-pass assertions, `TODO`, or `FIXME` markers.

## Backend Probe Scenario Manual Update: 2026-06-01

- `doc/06_spec/unit/lib/gpu/engine2d/backend_probe_strict_spec.md` mirrors the 8 strict backend probe scenarios, including the new runtime evidence fields for Metal, Vulkan, CUDA, and CPU SIMD architecture lanes.
- Added a manual-purpose section explaining that the spec prevents strict backend requests from silently falling back to CPU and makes backend-specific runtime evidence visible for rendering/layout-comparison performance triage.
- Focused verification after manual review:
  - `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/gpu/engine2d/backend_probe_strict_spec.spl --mode=interpreter --clean`: 1 file, 8 tests, 0 failures; runner duration 1465ms.
  - `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.
  - Placeholder scan over `backend_probe.spl`, `backend_probe_strict_spec.spl`, and the backend probe manual found no live `pass_todo`, false-pass assertions, `TODO`, or `FIXME` markers.

## Research Conclusion

The repo already has enough capture, comparison, backend, and system-test scaffolding to harden incrementally. The next design should make comparison status explicit, preserve capture failures as first-class diagnostics, separate structural/layout comparison from pixel/perceptual comparison, and require backend performance evidence to be hardware-qualified rather than inferred from source presence.

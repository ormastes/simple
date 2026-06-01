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

- `SIMPLE_LIB=src bin/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src bin/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src bin/simple test test/system/gui/glass_pixel_compare_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src bin/simple test test/system/gui/tui_screen_spec.spl --mode=interpreter`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

## Research Conclusion

The repo already has enough capture, comparison, backend, and system-test scaffolding to harden incrementally. The next design should make comparison status explicit, preserve capture failures as first-class diagnostics, separate structural/layout comparison from pixel/perceptual comparison, and require backend performance evidence to be hardware-qualified rather than inferred from source presence.

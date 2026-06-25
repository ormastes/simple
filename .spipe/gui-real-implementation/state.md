# Feature: gui-real-implementation

## Raw Request
$sp_dev impl real plan gui_real_impl....plan.md

## Task Type
feature

## Refined Goal
Implement the real shared Simple GUI window-manager stack described in `doc/03_plan/gui_real_implementation_plan_2026-06-01.md` so hosted macOS and AArch64-HVF QEMU use shared WM lifecycle state, Simple Web MDI content, Engine2D-backed rendering, and explicit backend evidence instead of direct-buffer demos.

## Acceptance Criteria
- AC-1: `src/os/hosted/hosted_entry.spl` compiles and launches a hosted macOS shared WM path using real hosted backend/input modules, not stale imports or square-only demos.
- AC-2: Hosted macOS and QEMU SimpleOS consume the same shared MDI setup for Terminal, Editor, Browser, File Manager, and Calculator surfaces.
- AC-3: Shared WM lifecycle state owns create, focus, move, resize, minimize, restore, close, z-order, hit testing, drag state, and keyboard/pointer routing.
- AC-4: Non-overlay MDI client areas render via `WebRenderRequest.with_pixel_output()` and `simple_web_window_renderer.spl`, not hand-coded title/body strings or hardcoded framebuffer browser panels.
- AC-5: Simple Web pixels and compositor chrome pass through Engine2D/CompositorBackend contracts before presentation, with batched or bulk blit paths on hot presentation paths.
- AC-6: Backend evidence reports state selected backend, fallback reason, frame time, and readback status, and fail closed instead of silently reporting CPU fallback as Metal/GPU/QEMU SIMD success.
- AC-7: macOS hosted launch through `scripts/macos-gui-run.shs` opens the shared hosted WM in a visible full-size `.app` window with readable Simple Web MDI content.
- AC-8: Pointer drag changes a window position through shared lifecycle state, and keyboard focus, close, minimize, restore, and theme/content actions re-render visibly.
- AC-9: AArch64-HVF QEMU boots to the same MDI scene and produces an authoritative QMP screenshot capture with backend evidence.
- AC-10: Acceptance gates pass: `SIMPLE_LIB=src bin/simple check src/os`, `SIMPLE_LIB=src bin/simple check src/lib`, and `SIMPLE_LIB=src bin/simple check examples/simple_os/hosted`.
- AC-11: Verification specs or evidence cover lifecycle actions, Simple Web pixel flow through Engine2D, QEMU browser/client pixels from `WebRenderArtifact.pixels`, backend selection/fail-closed behavior, macOS hosted visual inspection, and AArch64-HVF QEMU visual capture.
- AC-12: Required documentation links and launch guidance are updated in the plan, architecture, GUI layer contract, UI stack guide, and AArch64 QEMU guide only after corresponding implementation evidence exists.

## Scope Exclusions
Existing direct-buffer demos may remain only if clearly labeled smoke-only and excluded from release evidence.

## Phase
dev-done

## 8K Multi-Framework Benchmark (2026-06-05)

Cross-framework 8K (7680x4320) GUI perf comparison added:
- 7 backends: Pure Simple CUDA, Simple Web Software, Electron, GTK3/C, JS/Node, JS/Browser, Python/tkinter
- Runner: `tools/gui_perf_bench/run_all_benchmarks.shs`
- Guide: `doc/07_guide/platform/gui_perf_benchmark_comparison.md`
- Pixel parity gate enforced for all optimizations (exact match, no tolerance)

## Log
- dev: Created state file with 12 acceptance criteria (type: feature).
- benchmark: Added 8K multi-framework GUI perf comparison harness with 7 backends and guide doc.

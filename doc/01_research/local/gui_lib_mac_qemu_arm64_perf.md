<!-- codex-research -->
# GUI Lib macOS + SimpleOS QEMU ARM64 Perf Local Research

## Scope

Validate Simple GUI library sanity, drawing consistency, capture comparison, and performance on the macOS host and the SimpleOS QEMU ARM64 path, with special attention to Metal-accelerated 2D rendering and pure-Simple implementation hot paths.

## Existing Artifacts

- SPipe state: `.spipe/gui-lib-mac-qemu-arm64-perf/state.md`.
- Current plan context: `doc/03_plan/gui_hardening_current_plan_2026-06-01.md` says GUI hardening already has local evidence and remaining work.
- Architecture context:
  - `doc/04_architecture/simple_gui_stack.md` separates Simple GUI model, WM/desktop shell, compositor, host/web adapters, Simple Web Renderer, and Engine2D.
  - `doc/04_architecture/gui_layer_contract.md` locks `CompositorBackend`, `InputBackend`, and Engine2D boundaries.
  - `doc/04_architecture/arm32_jit_metal_constraints.md` records that Metal is an AArch64/macOS path, not ARM32.
  - `doc/04_architecture/simpleos_arm_qemu_fs_toolchain_verification.md` covers ARM QEMU verification boundaries.
- Prior related research: `doc/01_research/local/gui_color_image_pipeline_8k.md`, `doc/01_research/domain/gui_color_image_pipeline_8k.md`, and `doc/01_research/local/performance_visual_comparison.md`.

## Source Surfaces

- GUI/render shell:
  - `src/os/gui/render.spl`
  - `src/os/gui/render_shapes.spl`
  - `src/os/gui/render_effects.spl`
  - `src/app/editor/gui_shell_core.spl`
  - `src/app/editor/gui_shell_render.spl`
- Compositor/WM:
  - `src/os/compositor/compositor.spl`
  - `src/os/compositor/compositor_engine2d.spl`
  - `src/os/compositor/wm_scene.spl`
  - `src/os/compositor/wm_action_applier.spl`
  - `src/os/compositor/wm_consistency_runner.spl`
  - `src/os/desktop/wm_runtime_bridge.spl`
- Engine2D and Metal:
  - `src/lib/gc_async_mut/gpu/engine2d/engine2d_api.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/engine2d_session.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/metal_session.spl`
  - `src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl`
  - `src/lib/gc_async_mut/io/metal_sffi.spl`
  - `src/lib/nogc_sync_mut/io/metal_sffi.spl`
- QEMU/capture:
  - `src/os/qemu_runner.spl` and parts 1-5
  - `src/os/compositor/qemu_capture.spl`
  - `src/app/vm/qemu_manager.spl`

## Test and Script Surfaces

- Host and Metal checks:
  - `scripts/macos-gui-run.shs`
  - `scripts/check-metal-generated-2d-readback.shs`
  - `scripts/check-metal-engine2d-framebuffer-readback-evidence.shs`
  - `test/perf/graphics_2d/metal_smoke_spec.spl`
  - `test/perf/graphics_2d/bench_2d_metal_simple.spl`
  - `test/perf/graphics_2d/bench_2d_metal_simple_jit.spl`
  - `test/perf/graphics_2d/perf_2d_runner.spl`
- QEMU and capture checks:
  - `scripts/check-simpleos-arm64-wm-qemu-readiness.shs`
  - `scripts/check-wm-launch-capture-evidence.shs`
  - `scripts/check-qemu-gtk-wm-capture-evidence.shs`
  - `scripts/check-qemu-capture-fake-qmp-evidence.shs`
  - `test/system/gui/arm64_wm_qemu_contract_spec.spl`
  - `test/system/gui/wm_input_qemu_smoke_spec.spl`
  - `test/system/engine2d_in_qemu_spec.spl`
  - `test/system/app/os/feature/engine_2d_qemu_spec.spl`
- Visual baselines:
  - `test/baselines/engine2d_in_qemu`
  - `test/baselines/browser_in_qemu`
  - `test/baselines/simpleos_desktop_framebuffer`
  - `test/baselines/simpleos_desktop_with_apps_framebuffer`
  - `test/baselines/wm_compare/engine2d_in_qemu`
- Performance comparisons:
  - `test/perf/graphics_2d/*`
  - `test/perf/tauri_equiv/*`
  - `test/perf/web_render_chrome/*`
  - `test/integration/rendering/perf_smoke_spec.spl`
  - `test/integration/rendering/wm_perf_spec.spl`

## Local Risks

- QEMU live capture requires a running VM with a QMP socket; existing scripts can mark it unavailable unless strict mode is enabled.
- Metal readback can pass while presentation pacing still stalls; command-buffer and drawable lifetime probes must be included in perf evidence.
- Pure-Simple performance work must stay in `.spl` source and avoid moving correctness into C/Rust helpers.
- Visual comparison must distinguish meaningful drawing regressions from platform capture noise.

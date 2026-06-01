# Real macOS WM Implementation Plan - 2026-06-01

<!-- codex-design -->

## Objective

Replace hosted/demo WM paths that draw directly into winit or local pixel arrays
with one real shared stack:

```text
hosted macOS WM / AArch64-HVF QEMU WM
  -> shared WM lifecycle and MDI surfaces
  -> Simple Web Renderer app content
  -> Simple 2D / Engine2D primitive renderer
  -> backend: Metal on macOS, CPU SIMD fallback, QEMU framebuffer CPU SIMD
```

The current square-only or direct-buffer demos are useful smoke tests, but they
are not release evidence for the real WM. Release evidence must prove readable
text, draggable/resizable/focusable windows, input dispatch, Simple Web content,
and the selected render backend.

## Current Findings

- `src/os/hosted/hosted_entry.spl` is the intended hosted desktop entry, but it
  imports stale `os.compositor.hosted_backend` and `hosted_input_backend` names
  while actual hosted backend files are Cocoa/SDL2/Win32 variants.
- `examples/simple_os/hosted/hosted_wm_software.spl` is runnable, but explicitly
  duplicates render logic and presents software pixels through winit. It is not
  the target shared WM path.
- QEMU/SimpleOS WM entrypoints exist under `examples/simple_os/arch/x86_64/`
  and `examples/simple_os/arch/arm64/wm_entry.spl`, but several are
  self-contained local WMs with direct framebuffer or `rt_gui_*` drawing.
- Shared WM logic exists in `src/os/compositor/compositor.spl`,
  `src/os/services/wm/wm_service.spl`, and
  `src/os/compositor/wm_action_applier.spl`.
- Simple Web app content adapter exists in
  `src/os/compositor/simple_web_window_renderer.spl`, but current live hosted
  paths can bypass it.
- `src/lib/common/ui/web_render_api.spl` already defines the shared
  `WebRenderRequest` and `WebRenderArtifact` envelope, and
  `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl` can map those requests
  to pixels.
- `src/lib/gc_async_mut/gpu/engine2d/backend.spl` defines the Simple 2D backend
  trait, and `engine.spl` has backend selection including Metal.
- Generic Simple Web layout currently paints through a pure framebuffer path and
  can ignore the backend name, so successful generic HTML rendering is not proof
  that Metal, CPU SIMD, or QEMU framebuffer backends were exercised.
- `examples/simple_os/arch/x86_64/gui_entry_engine2d.spl` claims a QEMU WM plus
  Simple Web direction, but its browser panel is still hardcoded framebuffer
  drawing rather than real `WebRenderRequest -> SimpleWebRenderer` pixels.
- `GpuCompositorBackend.get_pixel_buffer()` can return a zero buffer unless a
  test override is installed, so readback evidence must come from real backend
  readback or explicitly say it is unavailable.
- macOS QEMU performance lane must prefer `qemu-system-aarch64 -accel hvf`.
  x86_64 QEMU is compatibility coverage, not the primary macOS performance lane.

## Non-Negotiable Target Behavior

- One WM authority owns create, focus, move, resize, minimize, restore, close,
  z-order, hit testing, drag state, and input routing.
- Hosted macOS and QEMU SimpleOS use the same WM lifecycle state and MDI surface
  model.
- Window client areas render through `SimpleWebRenderer` request/artifact paths,
  not hand-coded title/body strings in hosted demos.
- Renderer output goes through Simple 2D / Engine2D backend contracts before
  presentation.
- macOS backend selection is Metal first when real submit/readback is available,
  then CPU SIMD fallback with explicit reporting.
- QEMU backend selection is framebuffer CPU SIMD on AArch64-HVF first.
- Unsupported backends fail closed with capability evidence. No silent CPU
  fallback may be reported as Metal, GPU, or QEMU SIMD success.

## Implementation Phases

### Phase 1 - Entry Point Repair

- Fix `src/os/hosted/hosted_entry.spl` imports to use real hosted backend and
  input modules.
- Add a single hosted launch entry for macOS that constructs the shared
  `Compositor` + `WmService` + hosted backend pair.
- Remove the direct demo WM from manual evidence paths or label it smoke-only.
- Keep `scripts/macos-gui-run.shs` as the `.app` launcher, but make its default
  inspection target the shared hosted entry, not a direct-buffer demo.

### Phase 2 - Shared MDI Surface Model

- Define one `WmSurfaceContent` contract for app content:
  `simple_web`, `raw_pixels`, `shell_overlay`, and `debug_placeholder`.
- Move MDI window creation for Terminal, Editor, Browser, File Manager, and
  Calculator into shared setup code consumed by hosted macOS and QEMU.
- Route pointer press/move/release, keyboard focus, tab cycle, close, minimize,
  restore, and resize through `wm_action_applier.spl`.
- Keep shell/taskbar overlays adapter-private only where boot safety requires it.

### Phase 3 - Simple Web Renderer Integration

- Make every non-overlay app client area produce a
  `WebRenderRequest.with_pixel_output()`.
- Use `simple_web_window_renderer.spl` to materialize pixels for hosted and QEMU
  surfaces.
- Replace QEMU hardcoded browser panels with
  `WebRenderRequest -> SimpleWebRenderer -> WebRenderArtifact.pixels`.
- Make generic HTML layout either emit Engine2D draw commands or paint through an
  Engine2D-backed pixel surface so backend selection is actually exercised.
- Replace hosted-demo hand text with actual Simple Web HTML/CSS surfaces.
- Add fixture-independent text, layout, and event examples so evidence is not
  just corpus fast-path success.

### Phase 4 - Simple 2D Backend Unification

- Route Simple Web pixels and compositor chrome through `CompositorBackend`
  backed by Engine2D.
- Stop per-pixel `fill_rect` blits on hot paths; add batched/blit primitives for
  `WebRenderArtifact.pixels`.
- Add a real framebuffer/QEMU bridge for dirty rect and bulk pixel blit. Per-pixel
  `fill_rect` is acceptable only in unit tests or tiny debug surfaces.
- Wire backend selection:
  - macOS hosted: Metal when available and verified, otherwise CPU SIMD.
  - macOS QEMU: AArch64-HVF framebuffer CPU SIMD.
  - x86_64 QEMU: compatibility framebuffer CPU SIMD.
- Record backend kind, fallback reason, frame time, and readback status in each
  evidence report.

### Phase 5 - AArch64-HVF QEMU WM Lane

- Promote `examples/simple_os/arch/arm64/wm_entry.spl` from no-mouse demo toward
  the shared WM lifecycle path.
- Use `qemu-system-aarch64 -accel hvf` on macOS, with ramfb or virtio display
  according to available guest support.
- Add QMP screenshot capture as the authoritative visual proof.
- Keep x86_64 QEMU as a secondary parity lane after AArch64 is green.

### Phase 6 - Verification And Manual Inspection

- Add unit tests for shared lifecycle actions: drag, resize, focus, z-order,
  close, minimize, restore.
- Add renderer tests proving `simple_web` MDI client pixels flow through
  Engine2D, not direct winit draw calls.
- Add QEMU tests proving the browser/client panel comes from
  `WebRenderArtifact.pixels`, not hardcoded framebuffer rectangles.
- Add backend tests proving generic HTML rendering reports and exercises the
  selected backend or fails closed when unsupported.
- Add macOS hosted visual evidence: screenshot, backend report, text visibility,
  window size/position, event response.
- Add AArch64-HVF QEMU visual evidence: boot log, QMP screenshot, backend report,
  same MDI surfaces visible.
- Manual inspection app must open the shared hosted WM and remain open long
  enough to test drag, focus, close, minimize/restore, keyboard input, and theme
  or content changes.

## Parallel Work Plan

- Agent A, WM lifecycle: repair hosted entry imports, consolidate hosted/QEMU MDI
  window setup, and move pointer/key actions through shared WM action helpers.
- Agent B, renderer bridge: make Simple Web app content produce Engine2D-backed
  pixels through `simple_web_window_renderer.spl`, replace QEMU hardcoded browser
  panels, and add a batched blit path.
- Agent C, backend capability: wire macOS Metal/CPU SIMD reporting and QEMU
  framebuffer CPU SIMD reporting with fail-closed fallback reasons; separate CPU
  mirror evidence from real Metal submit/readback evidence.
- Agent D, verification/docs: add SPipe/unit/system evidence and update guides
  only after the implementation path is real.

Workers must use disjoint write scopes and must not revert concurrent edits.

## Acceptance Gates

- `SIMPLE_LIB=src bin/simple check src/os`
- `SIMPLE_LIB=src bin/simple check src/lib`
- `SIMPLE_LIB=src bin/simple check examples/simple_os/hosted`
- macOS hosted shared WM opens in a visible `.app` window and shows readable
  Simple Web MDI content.
- Pointer drag changes a window position through shared lifecycle state.
- Keyboard focus and close/minimize/restore actions change shared lifecycle
  state and re-render.
- AArch64-HVF QEMU lane boots to the same MDI scene and produces a QMP capture.
- Evidence reports explicitly state selected backend and whether Metal, CPU SIMD,
  or QEMU framebuffer CPU SIMD was used.

## Documentation Updates Required

- `doc/03_plan/gui_hardening_current_plan_2026-06-01.md`: link this as the real
  WM implementation plan.
- `doc/04_architecture/simple_gui_stack.md`: clarify the required stack and
  backend fallback boundaries.
- `doc/04_architecture/gui_layer_contract.md`: update the matrix when the shared
  hosted and AArch64 QEMU lanes are wired.
- `doc/07_guide/ui_stack_guide.md`: replace direct-buffer demo guidance with the
  shared hosted WM launch path once Phase 1 is complete.
- `doc/07_guide/platform/simpleos_arm64_wm_qemu.md`: update after live
  AArch64-HVF boot/capture evidence exists.

# GUI Drawing Layer Variations — Plan

**Status:** Rows 1, 2, 3, 5, 6, 7, 8 ✅ Done (2026-04-14); Row 4 blocked on sys-gui-006 LIVE-GREEN · **Date:** 2026-04-14 · **Owner:** GUI stack WG

Goal: make the Simple GUI stack work under four host/runtime combinations
with the *same* application code. The compositor + widget tree + 2D engine
already exist (`src/os/compositor/`, `src/os/gui/`, `src/lib/common/ui/`,
`src/lib/gc_async_mut/gpu/engine2d/`); this doc enumerates which layer is
pure Simple vs. borrowed, maps each variation onto existing modules, and
lists the gaps we need to close.

## 1. Layer model

From top (app) to bottom (pixels):

```
  App             — os.apps.*,  examples/*
  ─────────────────────────────────────────────
  GUI Lib         — common.ui.widget / builder / session
                    common.ui.event, common.ui.layout
  ─────────────────────────────────────────────
  Window Manager  — os.services.wm, lib.nogc_sync_mut.play.wm
                    common.window_protocol
  ─────────────────────────────────────────────
  Compositor      — os.compositor.compositor + *_backend
  ─────────────────────────────────────────────
  2D Engine       — lib.gc_async_mut.gpu.engine2d
                    lib.common.render_scene
  ─────────────────────────────────────────────
  Display         — framebuffer | host surface | HTMLCanvas | BrowserWindow
```

An application **must not** import anything below the GUI Lib line. All
variation lives in how the Compositor and 2D Engine are wired to a display.

## 2. The four variations

### V1 — Pure Simple on SimpleOS (baremetal)

```
  App  →  common.ui.*  →  os.services.wm  →
  os.compositor (fb_backend)  →  engine2d (backend_software / backend_virtio_gpu / backend_baremetal)
  →  os.drivers.framebuffer / os.drivers.gpu
```

Existing pieces: `fb_backend.spl`, `compositor_engine2d.spl`,
`engine2d_display.spl`, `backend_software.spl`, `backend_virtio_gpu.spl`,
`backend_baremetal.spl`, `os/desktop/shell.spl` already wires this via
`sys-gui-006`/`sys-gui-007` baselines.

Gaps: GPU backend (`backend_virtio_gpu`) end-to-end in QEMU; cursor/input
on real hw; `wm_service` multi-window focus model (tracked by `sys-gui-007`).

### V2 — Pure Simple on a host OS (macOS / Windows / Linux / BSD)

```
  App  →  common.ui.*  →  os.services.wm  →
  os.compositor (hosted_backend + hosted_input_backend) →
  engine2d (backend_metal | backend_vulkan | backend_opengl | backend_cpu)
  →  host window (Cocoa / Win32 / Xlib / Wayland / BSD X)
```

Existing pieces: `hosted_backend.spl`, `hosted_input_backend.spl`,
`backend_metal`, `backend_vulkan`, `backend_opengl`, `backend_cpu`,
`doc/04_architecture/cross_platform_wm.md`.

Gaps:
- Concrete host window shims per platform (currently only linux/x11 path
  is exercised by CI). Need Cocoa + Win32 SFFI surfaces.
- Input plumbing for trackpad gestures / IME.
- `ui.none` → hosted mapping in `src/app/wm_compare/` so visual diffs
  are produced against V1.

### V3 — Pure Simple + Chromium host (no Node)

```
  App  →  common.ui.*  →  os.services.wm  →
  os.compositor (browser_compositor_backend / browser_backend) →
  engine2d (backend_software → HTMLCanvas / WebGPU bridge)
  →  Chromium BrowserWindow via CEF/embedded Chromium
```

Existing pieces: `browser_backend.spl`, `browser_compositor_backend.spl`,
`src/app/ui.browser`, `src/app/ui.web`, `src/app/ui.tui_web`,
`wm_compare/html_compat.spl`, `wm_compare/live_capture.spl`.

Gaps:
- An actual Chromium/CEF shell (today we use a headless browser harness).
  Decide: CEF binding vs. `simple_browser` subproject (see memory
  `project_browser_platform`).
- WebGPU path in `engine2d` (currently only software → canvas).
- Shared input event translation (`common.ui.event` ↔ DOM events).

### V4 — Electron host

```
  App  →  common.ui.*  →  os.services.wm  →
  os.compositor (electron_capture + browser_compositor_backend) →
  engine2d (backend_software) →  Electron BrowserWindow (main + renderer IPC)
```

Existing pieces: `electron_capture.spl`, `src/app/ui.electron`,
`doc/03_plan/ELECTRON_VSCODE_WASM_PLAN.md`.

Gaps:
- Main/renderer split: which parts run under nogc vs. gc_async_mut.
- File-system + notification bridges via `ui.ipc`.
- Reuse wm_compare to produce parity screenshots vs. V2/V3.

## 3. Cross-cutting invariants

1. **App ⇒ GUI Lib only.** Any app that touches `os.compositor.*` directly
   is a bug. `wm_compare` is the enforcement harness — add a lint there.
2. **GUI Lib ⇒ WM.** The widget layer must not call the compositor; it
   emits a scene + event requests to `wm_service`.
3. **WM ⇒ Compositor.** One `Compositor` trait, N backends. The trait
   lives in `os/compositor/mod.spl`; add a missing method check in CI.
4. **Compositor ⇒ 2D Engine.** All drawing goes through the `Engine2D`
   trait in `lib.common.render_scene.engine_trait`. No backend may bypass
   it (today `glass_effects.spl` partially does — flagged).
5. **Input** uses `os.gui.input_event` on every variation; backends
   translate native events into that enum.

## 4. Work plan

Ordered by unlock value. Each item ends with the artifact that proves it.

| # | Task | Variation | Artifact | Plan | Status |
|---|------|-----------|----------|------|--------|
| 1 | Lock `Compositor` + `Engine2D` trait surfaces; mark unstable methods | all | `doc/04_architecture/gui_layer_contract.md` | [gui_layer_contract.md](../04_architecture/gui_layer_contract.md) (locked); fix plan: [sys_gui/gui_layer_contract_fix_plan.md](./sys_gui/gui_layer_contract_fix_plan.md) | ✅ Done 2026-04-14 |
| 2 | Expand `wm_compare` to run the same scene through V1/V2 and diff | V1, V2 | `test/sys/wm_compare/v1_v2_parity_spec.spl` | [sys_test/wm_compare_v1_v2_parity.md](./sys_test/wm_compare_v1_v2_parity.md) | ✅ Done 2026-04-14 |
| 3 | Land Cocoa + Win32 hosted surfaces behind `hosted_backend` | V2 | `src/os/compositor/hosted_backend_cocoa.spl`, `_win32.spl` | [v2_hosted_engine2d_rewiring.md](./v2_hosted_engine2d_rewiring.md) (Phase C) | ✅ Done 2026-04-14 |
| 4 | virtio-gpu accelerated path in QEMU for V1 | V1 | `sys-gui-008` baseline in `doc/08_tracking/todo/` | not yet planned (sys-gui-008 tracker) | ⛔ Blocked on sys-gui-006 LIVE-GREEN |
| 5 | CEF or simple_browser shell driving `browser_compositor_backend` | V3 | `src/app/ui.chromium/main.spl` + parity screenshots | [v3_simple_browser_milestones.md](./v3_simple_browser_milestones.md) — Option B chosen per [v3_shell_choice_2026-04-14.md](../01_research/domain/v3_shell_choice_2026-04-14.md) | ✅ Done 2026-04-14 (M1–M12 all landed) |
| 6 | Electron main/renderer split using `electron_capture` + `ui.ipc` | V4 | `src/app/ui.electron/main.spl` green in `wm_compare` | not yet planned | ✅ Done 2026-04-14 |
| 7 | Shared input-event conformance suite across all four | all | `test/unit/common/ui/input_event_conformance_spec.spl` | [sys_test/input_event_conformance.md](./sys_test/input_event_conformance.md) | ✅ Done 2026-04-14 |
| 8 | Golden-image gate: same app, 4 backends, ≤1% perceptual diff | all | `doc/06_spec/app/compiler/feature/windows_spec.md` update | landed with Row 2 harness | ✅ Done 2026-04-14 |

> **Row 5 milestone trace (2026-04-14).** M1 skeleton `8b`, M2 input `cdd`,
> M3 CSS subset `56c`, M4 engine merge `07`, M5 wm_compare parity `5c`,
> M6 tab manager `26`, M7 interactivity `37` + real WebGPU `96`,
> M8 CSS extensions `ca`, M9 JS audit `cc`, M10 DevTools `05`,
> M11 snapshot/record-replay `0f`, M12 Acid2 reftest `9ef`. Plus Gpu native
> glass (D2 Phase 2) in `37`. Only remaining row is Row 4 (sys-gui-008
> virtio-gpu QEMU), still blocked on sys-gui-006 reaching LIVE-GREEN.

## 5. Decisions still open

- ~~**V3 shell choice:** CEF embedding vs. growing `examples/browser` into
  a usable Chromium-class shell. See memory `project_browser_platform`.~~
  **DECIDED — Option B (simple_browser).** See
  [v3_shell_choice_2026-04-14.md](../01_research/domain/v3_shell_choice_2026-04-14.md).
- ~~**GPU path for V2:** Vulkan everywhere vs. native (Metal/DX) per OS.
  Current modules favor both; pick per-platform default.~~
  **DECIDED — Metal on macOS, Vulkan on Linux + Windows + FreeBSD.** See
  [v2_gpu_defaults_2026-04-14.md](../01_research/domain/v2_gpu_defaults_2026-04-14.md).
- ~~**Electron packaging:** Are we shipping Electron as a first-class target
  or only as a dev preview? This changes whether V4 is in CI.~~
  **DECIDED — dev-preview only.** See
  [v4_electron_packaging_2026-04-14.md](../01_research/domain/v4_electron_packaging_2026-04-14.md).

## 6. Non-goals

- Designing a new widget toolkit. `common.ui.widget` + `builder` is the
  surface; this plan does not touch it.
- 3D (that is `lib.nogc_sync_mut.engine.render.renderer3d`, separate track).
- TUI variations — `ui.tui` / `ui.tui_web` already live under their own
  track and are not part of the drawing-layer story.

## Sub-plan index

This plan spawned the following sub-plans and research docs:

### Decided / locked
- Plan doc: this file (2026-04-14)
- Arch doc: [cross_platform_wm.md](../04_architecture/cross_platform_wm.md) — widened 2026-04-14
- Contract: [gui_layer_contract.md](../04_architecture/gui_layer_contract.md) — locked 2026-04-14
- Guide: [ui_stack_guide.md](../07_guide/ui_stack_guide.md)

### Decisions
- V3 shell choice → [v3_shell_choice_2026-04-14.md](../01_research/domain/v3_shell_choice_2026-04-14.md) — Option B
- V2 GPU defaults → [v2_gpu_defaults_2026-04-14.md](../01_research/domain/v2_gpu_defaults_2026-04-14.md)

### Implementation plans
- Contract fix plan → [gui_layer_contract_fix_plan.md](./sys_gui/gui_layer_contract_fix_plan.md)
- V2 hosted rewiring → [v2_hosted_engine2d_rewiring.md](./v2_hosted_engine2d_rewiring.md)
- V3 simple_browser milestones → [v3_simple_browser_milestones.md](./v3_simple_browser_milestones.md)
- wm_compare V1/V2 parity → [sys_test/wm_compare_v1_v2_parity.md](./sys_test/wm_compare_v1_v2_parity.md)
- Input-event conformance → [sys_test/input_event_conformance.md](./sys_test/input_event_conformance.md)

## 7. References

- [cross_platform_wm.md](../04_architecture/cross_platform_wm.md)
- [gui_layer_contract.md](../04_architecture/gui_layer_contract.md)
- [ui_stack_guide.md](../07_guide/ui_stack_guide.md)
- [v3_shell_choice_2026-04-14.md](../01_research/domain/v3_shell_choice_2026-04-14.md)
- [v2_gpu_defaults_2026-04-14.md](../01_research/domain/v2_gpu_defaults_2026-04-14.md)
- [sys_gui/gui_layer_contract_fix_plan.md](./sys_gui/gui_layer_contract_fix_plan.md)
- [v2_hosted_engine2d_rewiring.md](./v2_hosted_engine2d_rewiring.md)
- [v3_simple_browser_milestones.md](./v3_simple_browser_milestones.md)
- [sys_test/wm_compare_v1_v2_parity.md](./sys_test/wm_compare_v1_v2_parity.md)
- [sys_test/input_event_conformance.md](./sys_test/input_event_conformance.md)
- `doc/03_plan/sys_test/simpleos_small_complete_gui.md`
- `doc/03_plan/os_gui_hello_world.md`
- `doc/03_plan/ELECTRON_VSCODE_WASM_PLAN.md`
- `doc/08_tracking/todo/sys_gui_006_*` and `sys_gui_007_*`
- `src/os/compositor/`, `src/os/gui/`, `src/os/desktop/`
- `src/lib/gc_async_mut/gpu/engine2d/`, `src/lib/common/render_scene/`
- `src/app/wm_compare/`, `src/app/ui.*`

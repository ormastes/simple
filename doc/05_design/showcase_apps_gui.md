<!-- codex-design -->
# Showcase apps GUI design

The catalog presents three equal cards: **2D Rendering**, **Web Standards**, and **GUI Widgets**. Each card shows three surface badges—Standalone, Host WM, and SimpleOS WM—with `ready`, `blocked`, or `skipped` state derived from the canonical catalog rather than hardcoded UI text.

The 2D window is an 800x600 labeled gallery with rectangle/line, curve/shape, gradient/effect, image/text, clip, mask, and engine-composition sections. The web window uses normal browser chrome above the single standards page. The widget window retains its gallery, with interactive controls visibly changing state.

Host-WM and SimpleOS-WM windows keep the same content/title and add normal titlebar, focus, minimize/restore, close, and taskbar behavior. Failure views show app ID, surface, phase, and backend/transport cause; they never replace content with a plausible blank frame.

Identity contract used across docs/specs:

- `graphics_2d_showcase` → catalog title `2D Rendering Showcase`; runtime titles are backend-stamped:
  - `2d_showcase_backed_<backend_token>` (standalone)
  - `2d_showcase_backed_<backend_token>` (host/installed)
- `web_standards_showcase` → catalog title `Web Standards Showcase`; runtime titles are backend-stamped:
  - `web_showcase_backed_<backend_token>` (standalone)
  - `web_showcase_backed_<backend_token>` (host/installed)
- `gui_widget_showcase` → catalog title `Widget Showcase`; runtime titles are backend-stamped:
  - `gui_showcase_backed_<backend_token>` (standalone)
  - `gui_showcase_backed_<backend_token>` (host/installed)

Backend control contract:

- `widget_showcase_gui.spl` accepts `--backend=<name>` first, then `SIMPLE_GUI_BACKEND`, and defaults to `software`.
- `graphics_2d_showcase_gui.spl` and `wm_graphics_2d_showcase_gui.spl` honor `SIMPLE_GUI_BACKEND`; standalone defaults to `software`, while host-WM child defaults to `cpu_simd`.
- `web_standards_showcase_gui.spl` and WM-web counterpart honor `SIMPLE_GUI_BACKEND`; default is `cpu_simd`.
- Backend identifiers are canonicalized by the engine layer and normalized aliases (`cpu-simd` and `simd-cpu` are accepted as `cpu_simd`); unknown values fall back to `software`.

## WM showcase surface — intended GUI contract (2026-08-05)

The WM showcase presents the three showcase windows (2D, web, GUI widgets)
managed together, with a taskbar below them. **Written by the documentation
lane; the code is owned by a parallel lane and is not attested here.** Items are
marked *present* (read from the tree on 2026-08-05) or *intended* (contract for
the lane to satisfy, currently unverified).

### Windows

- *Intended.* Each showcase window keeps the same content and title it has
  standalone, and gains normal titlebar, focus, minimize/restore, maximize, and
  close behaviour — the existing Host-WM/SimpleOS-WM rule above, applied to all
  three at once rather than one window at a time.
- *Present.* Window lifecycle is the scalar FSM in
  `src/lib/common/ui/wm_window_state.spl`. `restore` requires the caller to pass
  the pre-minimize state (`wm_window_state_restore(state, state_before_minimize)`),
  so the chrome that offers "restore" must retain it.
- *Present.* `src/lib/common/ui/wm_full_stack_demo.spl` already composes a 2D
  render surface (handle `101`) and a web render surface (handle `102`) into one
  widget tree — it is a demo tree, **not** a window manager, and must not be
  presented as the WM showcase itself.

### Taskbar

- *Present.* The running-app row is **derived from live window state**:
  `build_taskbar_model` (`src/app/ui.web/taskbar_shell.spl:55`) iterates the
  `UiWindowSurfaceRegistry`'s `bindings`;
  `host_taskbar_runtime_taskbar_model` feeds it `session.window_surfaces`.
- *Present.* Pinned entries and tray items are **caller-supplied**, not derived.
  Pins are encoded by the `SIMPLE_TASKBAR_PINS_V1` line codec
  (`src/lib/common/ui/taskbar_pin_wire.spl`), which is a codec only — the
  runtime owns storage.
- *Intended.* Opening, minimizing, restoring, and closing a showcase window
  must change the taskbar row within the same frame the window state changes,
  because the row is a projection of the registry rather than a parallel list.
  **Not yet verified end-to-end**: the FSM and the derivation exist
  independently and this doc names no spec that composes them.
- *Anti-requirement.* A taskbar built from a literal `TaskbarModel` does not
  satisfy this contract. Two literals remain in the tree
  (`src/os/desktop/modern_wm_readiness.spl:606`,
  `src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl:148`) and
  are readiness/demo shells, not the live path.

### Capture verification

- *Present.* Evidence is a P6 PPM plus pixel-class counts
  (`non_background_pixels`, `bright_pixels`, `accent_pixels`, `ink_pixels`,
  `sample_checksum`) from
  `src/os/compositor/hosted_wm_capture_evidence.spl` and
  `wm_gui_window_drawing_evidence.spl`; QEMU-side capture is
  `qemu_capture.spl`; differencing is `screenshot_compare.spl`. Detail:
  `doc/05_design/showcase_apps.md` §"Capture evidence contract".
- *Rule.* A capture must carry an absolute oracle, never a bare equality between
  two frames from the same path, and never a memorized pixel table
  (`.claude/skills/spipe.md` §"Equality is not correctness"). A failure view
  shows app ID, surface, phase, and cause — it never degrades to a plausible
  blank frame.

### Readiness reporting

*Present, and load-bearing.* `showcase_catalog()`
(`src/lib/common/ui/showcase_catalog.spl`) currently reports
`standalone_ready = host_wm_ready = simpleos_wm_ready = false` for **all three**
apps, and `test/01_unit/lib/common/ui/showcase_catalog_spec.spl:55` asserts all
nine bits are `false`. The catalog — not a capture log, not this document — is
where a "the WM showcase works" claim becomes real, and flipping a bit is a
spec-visible change that must land with its evidence.

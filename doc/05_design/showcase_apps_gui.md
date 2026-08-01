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

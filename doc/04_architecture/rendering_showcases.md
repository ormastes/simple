# Architecture — Rendering Showcases

Date: 2026-09-24. Requirements: `doc/02_requirements/feature/rendering_showcases.md`
(REQ-001..REQ-011), NFRs in `doc/02_requirements/nfr/`. Research:
`doc/01_research/local/rendering_showcases.md` (grammar verdict §2 is binding:
no parameterized imports; trait hosts + `.ui.sdn` + env config are the
sanctioned sharing mechanisms).

## Decision summary

- **Interactive showcases** (2D core/extended, GUI full, WM full, primary
  tabs): host-agnostic core + `common.ui.screen_host.ScreenHost` trait seam +
  thin per-backend entries — extending the proven `src/app/ui_showcase/`
  pattern (`showcase_run(host, prefix, frames)`, `showcase_core.spl:671`).
- **Static shared content** (item list of all rendering items, aqua theme
  gallery): `.ui.sdn` data documents consumed by the TUI loader, the GUI
  loader, and the web-server GUI (`bin/simple ui web`, reusing
  `src/app/ui.web/server.spl` — REQ-001).
- **Tier split**: separate core/full(entry) files per lane; extended/full
  imports the core module (compile-time loading-overhead win, NFR-001).

## Components

```
examples/06_io/ui/rendering/
  rendering_<lane>_<tier>.spl      # thin entries: env parse + host construct + run
  rendering_items.ui.sdn           # shared item-list document (lane tags inline)
  rendering_switch.spl             # UI-base switch (TUI|GUI|webserver)
  doc.md                           # run-command table

shared cores (per family):
  examples/ui/rendering_2d_core/      # 2D core scene module (imported by extended)
  examples/ui/rendering_web_core/     # web core page module
  examples/ui/rendering_widgets_core/ # brief widget set (kernel/core subset)
  examples/ui/rendering_widgets_full/ # full widget set (all kinds)
  app.ui_showcase.showcase_core       # existing ScreenHost-driven core (reuse)

hosts:
  app.ui_showcase.hosts.host_gui      # existing (GuiRenderer)
  app.ui_showcase.hosts.host_wm       # existing WM *client* (file bridge)
  NEW app.ui_showcase.hosts.host_tui  # char-grid ScreenHost impl
  NEW host_webserver (or ui.web direct serve)  # HTTP+WS (REQ-001)
```

**WM lane asymmetry (REQ-010):** the WM entries are WM-*as-server*, not
ScreenHost clients — they own window management. Structure: `HostCompositor`
over `HeadlessHostCompositorBackend` (`src/os/compositor/host_compositor_core.spl`),
windows admitted via `apply_bridge_request(COMP_CREATE_WINDOW, …)`, chrome/
taskbar free from `taskbar_model()`, render via
`shared_wm_scene_render_to_backend`, present via `GuiRenderer` when
`SIMPLE_GUI=1`, else composed PPM (same honest-fail gates as
`src/app/wm_showcase`). A thin `ScreenHost` impl over a single-window
`HostCompositor` bridges the WM core into the trait seam so `rendering_switch`
can list it.

**GUI internal windows (REQ-011):** scene-level, above widgets — no
WidgetKind. `simple_gui_internal_window[_with_chrome_kind]` +
`simple_gui_internal_window_scene` (`common.ui.window_scene.spl:477-501`),
`wm_chrome_theme()`, invariant: backend/config glue only, never per-pixel FFI.

## Data flow

1. Entry parses env (`SIMPLE_SHOWCASE_*`, tier, backend, capture path).
2. Core builds the scene/tab data (tabs = data: list of `{id, title, tags}`).
3. Host presents: DrawIR→Engine2D (gui/2d), char grid (tui), SharedWmScene→
   compositor (wm), WidgetNode→HTML+WS (webserver), HTML/CSS→layout→paint
   (web).
4. Capture: PPM readback (2d/gui/wm) or HTML artifact (web) or HTTP probe
   (webserver) — honest-fail gates everywhere (no vacuous PASS).

## MDSOC layering

- `common.ui.*` — shared models (WidgetNode, DrawIr, ScreenHost, window_scene,
  themes). No lane imports downward.
- `app.ui_showcase` (gc_async_mut) — cores + hosts; the only place backend
  knowledge lives.
- `examples/ui/rendering_*` — example-owned shared cores (sibling-import
  resolver quirk documented in research §1 applies).
- Entries — env + main only.

## Error handling / degradation

- WM host `open` returns nil unless `SIMPLE_WM_APP_MODE=client` + frame path
  (existing honest-fail, keep).
- TUI item-list marks the 19 unrendered WidgetKinds `(no tui)` — no silent
  skips.
- Web image: local fixture only; missing fixture = loud error, no placeholder.
- All captures write checksum + provenance sidecar (wm_showcase convention).

## Loading-overhead architecture (NFR-001)

Core entries import only the core module; extended/full entries import core +
extended scenes. Closure census script (`scripts/check/check-rendering-showcase-closure.shs`,
new) counts compiled modules per tier; gate ratio ≤ 0.60.

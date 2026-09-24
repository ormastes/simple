# Rendering Showcases — Run Commands

Shared cross-lane subtree (`examples/06_io/ui/rendering/`). Ten showcase
entries (lane × tier), one shared item list, and one UI-base switch.
Headless runs use `SIMPLE_TIMEOUT_SECONDS=0` (no wall-clock limit); GUI/window
variants additionally honor `SIMPLE_GUI=1` per entry source.

## Showcase entries

| Entry | Lane / Tier | Description | Headless run command |
|---|---|---|---|
| `rendering_tui_core.spl` | tui / core | Core widget set (panel, text, button, list, menubar, statusbar, divider, progress) on the char-grid ScreenHost | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_tui_core.spl` |
| `rendering_tui_full.spl` | tui / full | All 25 TUI renderers + `(no tui)` markers for the unrendered WidgetKinds | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_tui_full.spl` |
| `rendering_gui_core.spl` | gui / core | Core widget set on the GUI ScreenHost (PPM capture default) | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_gui_core.spl` |
| `rendering_gui_full.spl` | gui / full | Full widget set + REQ-011 internal-window desktop (titled + borderless) | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_gui_full.spl` |
| `rendering_wm_core.spl` | wm / core | WM chrome/taskbar + internal windows, compositor-owned, headless PPM | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_wm_core.spl` |
| `rendering_wm_full.spl` | wm / full | WM bridge admission of showcase windows + taskbar + sabotage gates | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_wm_full.spl` |
| `rendering_2d_core.spl` | 2d / core | Engine2D primitives, gradients, text+fonts (bitmap vs vector), word spacing | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_2d_core.spl` |
| `rendering_2d_extended.spl` | 2d / extended | Images, compositing, draggable overlapping panels, hit-tested click button | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_2d_extended.spl` |
| `rendering_web_core.spl` | web / core | Browser-engine page: multi-line text, `<img>` fixture, scrollbar region | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_web_core.spl` |
| `rendering_web_extended.spl` | web / extended | Tabs: forms-media, animation, aqua/glass/ios theme gallery | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_web_extended.spl` |
| `rendering_webserver.spl` | webserver / full | Web-server GUI: item list served by the pure-Simple HTTP server (REQ-001); bounded serve, self-exits after one GET | `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_webserver.spl` |

## Shared item list — web-server GUI (REQ-001)

The shared item list `rendering_items.ui.sdn` is served three ways: TUI sdn
loader, GUI sdn loader, and the `ui web` web-server GUI:

```
bin/simple ui web examples/06_io/ui/rendering/rendering_items.ui.sdn --port 8080
```

Then open http://localhost:8080 — one HTTP GET returns 200 with an item
marker (NFR-002 webserver probe).

## UI-base switch (REQ-004)

`rendering_switch.spl` reads `SIMPLE_RENDERING_UI=tui|gui|web` (default
`tui`) and drives the same `rendering_items.ui.sdn` through the matching
loader:

```
SIMPLE_RENDERING_UI=tui SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_switch.spl
SIMPLE_RENDERING_UI=gui SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_switch.spl
SIMPLE_RENDERING_UI=web SIMPLE_TIMEOUT_SECONDS=0 bin/simple run examples/06_io/ui/rendering/rendering_switch.spl
```

- `tui` runs the parser-backed TUI sdn loader in-process.
- `gui` spawns `bin/simple ui gui <items>` (auto-detected GUI backend);
  honest-fails if no display/runtime is available.
- `web` spawns `rendering_webserver.spl` — the pure-Simple HTTP server
  (REQ-001, no dependency on the `ui web` CLI) — sends a real GET probe,
  prints http://localhost:8080, and honest-fails on bind/spawn failure.

## Environment knobs

| Knob | Values | Purpose |
|---|---|---|
| `SIMPLE_RENDERING_UI` | `tui` \| `gui` \| `web` | UI-base switch selection |
| `SIMPLE_SHOWCASE_W` / `SIMPLE_SHOWCASE_H` / `SIMPLE_SHOWCASE_FRAMES` | ints | Showcase geometry/frame budget |
| `SHOWCASE_RESOLUTION` | `4k` \| `8k` \| `WxH` | Capture resolution |
| `SIMPLE_SHOWCASE_CAPTURE` | path | PPM capture output |
| `SIMPLE_GUI` | `1` | Physical window instead of headless PPM |
| `SIMPLE_2D_BACKEND` | `cpu` \| `cpu_simd` \| `vulkan` \| `metal` | Engine2D backend — **default `vulkan`** on lanes that construct one (2d, web; 2d admission is exact — an unavailable backend is `showcase status=blocked`, never a silent fallback). Advisory on gui/wm headless captures (CPU raster / compositor pixel buffer by design). |
| `SIMPLE_RENDERING_WEB_FIXTURE` | `1` | Generate `rendering_fixture.png` once |

## Honest-fail convention

Every entry exits non-zero with a single-line reason, in the shared format:

```
showcase status=blocked <reason>
showcase status=pass <path>
```

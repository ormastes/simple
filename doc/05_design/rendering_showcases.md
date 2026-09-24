# Detail Design — Rendering Showcases

Date: 2026-09-24. Architecture: `doc/04_architecture/rendering_showcases.md`.
Everything below lands under `examples/06_io/ui/rendering/` unless noted.

## Shared cores

**`examples/ui/rendering_widgets_core/`** — brief tier. Widget set (kernel/
core subset, matches the composition-kernel boundary from the
`ui_slim_kernel_plugin` expert): `panel, text, button, list, menubar,
statusbar, divider, progress`. One column, deterministic layout, `dark` theme
default.

**`examples/ui/rendering_widgets_full/`** — full tier. All 30 TUI-rendered
kinds + all 43 `WidgetKind`s for GUI/DrawIr (enum verified 2026-09-24: 43
variants, not 44; TUI dispatch covers 30, leaving 13 kinds with `(no tui)`
tags — design-doc census corrected from the earlier 44/25/19 estimate). Tab
data lives here as
`rendering_tabs() -> [{id, title, tags}]`, consumed by every lane (shared tabs,
changed tags only).

**`examples/ui/rendering_2d_core/`** — core scene module: `rendering_2d_core_scene(engine, w, h)`
drawing, in labeled grid cells: clear/rect/rect_filled/rect_list_filled/
rect_thick, line, circle/circle_filled/circle_thick, ellipse/arc, triangle
filled/outline, polygon, polyline, bezier, rounded rect (+
outline), gradient_rect (+h/stops), radial gradients, blur_rect, shadow_rect;
text group: `draw_text`, `draw_text_bg`, `draw_text_configured`, glyph run —
**bitmap font (5x7/8x16 fallback) vs vector corpus font side by side**,
word-spacing demo via `draw_shaped_text*` with `word_spacing_px` from
`nogc_sync_mut.text_layout.font_types` (gap: no engine param — do NOT fake it
with spaces).

**`examples/ui/rendering_2d_extended/`** — imports core; adds: images
(`draw_image*`), nested compositing (`draw_engine*`), masks/clips/blend modes,
offscreen + `read_pixels`; **draggable overlapping panel** (two translucent
panels, z-overlap; app-level pointer tracking via `host_pointer_down/move/up`
with a `drag_offset` state — same pattern as the existing showcase slider; no
engine drag API, gap recorded); **click-event button** using compositor
hit-testing (`compositor_pick_topmost` / `hit_rect`), with a click counter
rendered on screen.

**`examples/ui/rendering_web_core/`** — core page module: one HTML document,
multiple text lines (block + inline + styled spans), one `<img>` pointing at
the generated fixture `rendering_fixture.png`, and a scrollable region
exercising the UA scrollbar (`paint.spl:277-336`). Fixture is produced by the
extended entry once (`SIMPLE_RENDERING_WEB_FIXTURE=1`) via an engine2d render +
PNG write; absent fixture = loud error.

**`examples/ui/rendering_web_extended/`** — imports core page; adds tabs:
forms-media, animation, **theme gallery** (one section per current theme:
`aqua_light, aqua_dark, glass_light, glass_dark, glass_obsidian_light,
glass_obsidian_dark, ios_light, ios_dark, dark, light` — applied via CSS
variables, mirroring `demo_themes.ui.sdn`), and the GUI-rendered examples
ported to web (each full-tier widget rendered as HTML through the same tab
data).

## The ten entries

Each entry: header comment (lane, tier, shared-core dependency), env parse,
host/scene construct, run, capture. Env conventions inherited:
`SIMPLE_SHOWCASE_W/H/FRAMES`, `SHOWCASE_RESOLUTION`, `SIMPLE_SHOWCASE_CAPTURE`
(PPM path), `SIMPLE_GUI=1` (physical window), tier never via env (files are
the split). Backend selection: `SIMPLE_2D_BACKEND=cpu|cpu_simd|vulkan|metal`,
default **vulkan** on lanes that construct an Engine2D backend (2d core/
extended, web core/extended — exact admission, `showcase status=blocked` when
unavailable); gui/wm entries document it as advisory because their headless
captures are CPU-raster / compositor pixel-buffer by design.

- `rendering_tui_core.spl` / `rendering_tui_full.spl` — NEW `host_tui`
  (char-grid ScreenHost over `app.ui.tui` screen); brief renders the core set,
  full renders all 30 TUI-rendered kinds + `(no tui)` markers for the
  13 unrendered kinds (census corrected 2026-09-24: 43 enum variants).
- `rendering_gui_core.spl` / `rendering_gui_full.spl` — `host_gui` (existing);
  full adds the REQ-011 internal-window desktop (one `titled`, one
  `borderless` window) rendered via `shared_wm_scene_render_to_backend`.
- `rendering_wm_core.spl` — WM chrome/taskbar + 1–2 internal windows,
  compositor-owned, headless PPM default.
- `rendering_wm_full.spl` — WM opens its window by default, then admits the
  showcase windows (gui core/full content, 2d core scene, web core page) as
  internal windows through the file bridge; taskbar tracks them; sabotage
  sequence (close one → taskbar entry vanishes → restore) with checksum
  gates, mirroring `src/app/wm_showcase/session.spl`.
- `rendering_2d_core.spl` / `rendering_2d_extended.spl` — Engine2D scenes
  above; backend via `SIMPLE_2D_BACKEND` (default `cpu_simd` headless),
  PPM capture default.
- `rendering_web_core.spl` / `rendering_web_extended.spl` — browser-engine
  render of the pages above to PPM/HTML artifact; blocked until the
  `_level_rank` compile defect (REQ-009 note) is resolved.

## Cross-lane entries

- `rendering_items.ui.sdn` — item-list document: every rendering item with
  lane tags (`tui/gui/wm/2d/web`, `(no tui)` where true). Served three ways:
  TUI loader, GUI loader, `bin/simple ui web rendering_items.ui.sdn --port
  8080` (REQ-001, web-server GUI).
- `rendering_switch.spl` — UI-base switch: `SIMPLE_RENDERING_UI=tui|gui|web`
  (web = spawn `ui web` server and print its URL); one definition, three
  presentations, demonstrating the ScreenHost seam end to end.

## Error handling

All entries exit non-zero with a single-line reason on: missing fixture,
unavailable backend (honest-fail, no stub fallback unless
`SIMPLE_NO_STUB_FALLBACK` unset AND degraded mode explicitly logged), capture
write failure. Captures carry checksum + provenance sidecar.

## Verification hooks (NFR-002)

- Compile gate: `bin/simple check <entry>` for all 10 + switch.
- Captures: 2d/gui/wm entries write PPM (nonzero checksum assert); web writes
  HTML artifact containing all tab ids; webserver probe: one HTTP GET returns
  200 + item marker.
- Closure census: `scripts/check/check-rendering-showcase-closure.shs` prints
  per-tier module counts + ratio (gate ≤ 0.60).

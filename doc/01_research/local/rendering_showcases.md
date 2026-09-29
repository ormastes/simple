# Local Research — Rendering Showcases (consistency + LLM-wiki documentation)

Date: 2026-09-24. Feature lane: `rendering-showcases-20260924`.
Question: how to make the TUI/GUI/2D/Web (+new web-server) rendering showcases
consistent, shared, and wiki-documented. Supersedes nothing; prior showcase
research: `doc/01_research/local/ui_showcase_feature_screens.md`.

## 1. Current state (verified by inspection)

`examples/06_io/ui/` holds 103 entries. Showcase naming: `<name>.spl` headless,
`<name>_gui.spl` windowed, `wm_<name>_gui.spl` WM-hosted, `*_entry.spl` backend
probe, `*.ui.sdn` declarative layout. Readiness registry:
`src/lib/common/ui/showcase_catalog.spl`.

**Sharing mechanisms that already exist (and work):**

- `src/app/ui_showcase/showcase_core.spl` — ONE host-agnostic definition
  (widget tree builders `showcase_build_sized`, reducer `showcase_apply`,
  DrawIR scene `showcase_scene`, probes `SC_PROBE_CLICK/DRAG/KEYS/INPUT`,
  counters `showcase_click_count`/`showcase_drag_count`) driven by
  `showcase_run(host: ScreenHost, prefix, max_frames)` (line 671). Hosts:
  `host_2d.spl`, `host_gui.spl`, `host_web.spl`, `host_wm.spl` — trait
  `common.ui.screen_host.ScreenHost` (`src/lib/common/ui/screen_host.spl:32`).
  **No `host_tui` exists** (host_web.spl header: "ScreenHost impl #4 of 4"),
  and `host_web.spl` does NOT bind HTTP — it writes HTML to a file.
- `.ui.sdn` declarative format — one data file consumed by web/electron/tauri
  runners via `parse_ui_to_tree` (`render_mobile_page.spl:15`); theme embedded
  (`app: title/theme`). Demo sets already exist: `demo_basics`, `demo_controls`,
  `demo_layouts`, `demo_themes`, `demo_kitchen_sink`, etc.
- Engine2D backend entries share one scene: `engine2d_backend_{cpu_simd,metal,vulkan}_entry.spl`
  all call `run_engine2d_scene_backend(backend, ...)` from
  `examples.ui.engine2d_backend_scene`.
- Older style (being retired): `widget_showcase_gui.spl` vs
  `widget_showcase_metal_gui.spl`; still-duplicated twins:
  `responsive_showcase{,_metal}_gui.spl`; partial-share wart:
  `graphics_2d_showcase_gui.spl` copy-pastes ~50 env lines from
  `graphics_2d_showcase.spl`.

**Core/extended split: NOT done** for 2D or web. No `*_core`/`*_extended`
files exist. Only env knobs: `SHOWCASE_RESOLUTION`/`SHOWCASE_DPI`
(`graphics_2d_showcase.spl:28-38`), `SIMPLE_GUI_BACKEND` override.

## 2. Grammar verdict — can Simple share one definition across backends?

**No parameterized modules/functors.** `parse_use_decl`
(`src/compiler/10.frontend/core/parser_decls_use.spl:110-249`) supports paths,
wildcards, name lists/aliases, `lazy` — no argument expressions. No `cfg`-style
user conditional compilation (`@cfg` is arch-only preprocessing,
`src/compiler/10.frontend/frontend.spl:19-27`).

**What IS supported (sufficient, proven in-tree):**
- Traits with first-class trait values — backend as a runtime argument
  (`showcase_run(host: ScreenHost, ...)`) is the canonical zero-duplication seam.
- First-class fn types (`type HttpHandler = fn(HttpRequest) -> HttpResponse`,
  `src/lib/web/http/server.spl:138`) — data-driven (label, fn) item lists work.
- Generics (compile-time monomorphization, `src/compiler/40.mono/`) — for
  type-level sharing, not backend tags.

**Conclusion:** import-time sharing (`use showcase.{backend=tui}`) would need a
new functor-like language feature — NOT required. Runtime trait hosts + env
config + `.ui.sdn` data files achieve the goal. This answers the user's
"check grammar; if not support proper sharing tell me": the grammar does not
support *parameterized imports*, and it doesn't need to — the repo's own
converged pattern (host-agnostic core + ScreenHost impls) is the sanctioned
mechanism. A functor mechanism (extension to `decl_use_import` + instantiation
cache in `40.mono/`) is the concrete feature request if import-time sharing is
ever wanted.

## 3. Capability inventory (for showcase content)

**TUI** (`app.ui.render.tui_widgets` → `app.ui.render._TuiWidgets.{core_widgets,extended_widgets}`):
25 renderers — panel, text, list, table, progress, menubar, statusbar, input,
tabs, button, checkbox, radio, dropdown, textfield, image, divider, dialog,
tooltip, scroll (core); textarea, heading, navigation_bar, tab_bar, card,
switch, segmented_control, search_bar (extended). GAP: `WidgetKind` has 44
kinds; 19 (sidebar, command_bar, command_palette, toast, sheet_modal,
context_menu, inspector, utility_rail, status_chip, selection_pill,
empty_state, glass_title_bar, …) have NO TUI renderer.

**GUI**: no separate widget library — same WidgetNode tree →
`widget_draw_ir.spl` → DrawIrV3Scene → Engine2D; window via
`std.io.window_winit` (`WinitLoop`, `winit_poll_input`) or `GuiRenderer`.

**Engine2D** (`class Engine2D`, `src/lib/gc_async_mut/gpu/engine2d/engine.spl:269`):
full primitive set (rect/line/circle/ellipse/arc/triangle/polygon/polyline/
bezier/rounded/thick), gradients (linear/h/stops, radial, blur, shadow, glass),
text (`draw_text*`, `draw_glyph_run`, `draw_shaped_text*`, `load_font*`,
`select_font_identity`, `font_cache_stats`), images (`draw_image*`,
`draw_engine*` nested compositing), masks/clips/blend, offscreen engines,
`read_pixels*`, damage tracking, compositor with z-order + hit-testing
(`compositor.spl`, `compositor_pick_topmost`). Fonts: google-fonts corpus
(`assets/fonts`, `font_registry.spl`), 5x7/8x16 bitmap fallback glyphs,
stb_truetype vector path. GAPS: no word-spacing param on `draw_text*` (spacing
lives in `text_layout/font_types.spl:56,70,177 word_spacing_px`; reachable via
shaped runs / advance arrays); no engine-level drag API (app-level from
`host_pointer_down/move/up`, as the existing slider proves); 2D/vector split:
bitmap fallback vs corpus vector fonts via `load_font`.

**Web renderer** (`src/lib/gc_async_mut/gpu/browser_engine/`): HTML/CSS subset
inventory in `web_renderable_feature_inventory.spl` (block/inline text, layout,
paint, forms-media, animation); `<img>` via local paths (`resource_loader.spl`);
scrollbar SUPPORTED (`paint.spl:277-336`, UA 15px); CSS custom properties
(`style/custom_properties.spl:278`); multiple documents via `browsing_context.spl`
(no browser tab strip UI; `web_showcase_tabs.spl` is showcase-owned tab UI).
GAP: no data-URI image decode found — image showcase needs a local fixture file.

**Themes** (user wrote "aquare"): real names are **`aqua_light` / `aqua_dark`**
(`common.ui.glass.theme`), plus `glass_light`, `glass_dark`,
`glass_obsidian_light`, `glass_obsidian_dark`, `ios_light`, `ios_dark`,
`dark`, `light` (TUI palettes, `app.ui.render.colors.spl`), token-tier
`celestial_ether` / `aetheric_dark`. DrawIr dispatch:
`widget_draw_ir_theme_from_name` (`widget_draw_ir.spl:135`); existing theme
demo asset: `demo_themes.ui.sdn`.

**Web-server GUI (new backend, requirement 0):** TWO reusable owners:
- `src/app/ui.web/server.spl` — `WebServer` (HTTP + WebSocket live updates,
  session tokens, OriginGuard; renders a `UISession` from `.ui.sdn` to HTML).
  Entry: `bin/simple ui web <file.ui.sdn> [--port N]`. Example:
  `examples/06_io/ui/hello_web.spl` (port 8080).
- `src/app/ui.tui_web/` — `TuiWebServer`: TUI screen → HTML
  (`screen_to_html.spl`), HTTP + WebSocket, file-watch reload. Entry:
  `bin/simple ui tui_web <file.ui.sdn> --port N`.
Both serve a rendered UI in a real browser — this is the "webserver GUI".

## 4. Infra constraints (affect verification)

- `bin/simple` is a symlink to the Rust seed
  (`src/compiler_rust/target/bootstrap/simple`) — violates the default-tooling
  rule; the deployed `bin/release/aarch64-apple-darwin/simple` (Jul 25) cannot
  parse current stdlib (`src/lib/nogc_sync_mut/io/process_ops.spl`, changed
  2026-09-14) — it is effectively an old seed build. The CURRENT seed compiles
  current stdlib fine.
- Example watchdog: 10s default, `SIMPLE_TIMEOUT_SECONDS=N` raises it, `=0`
  disables. Graphics-stack compiles exceed 4 min under the seed — showcase
  verification needs `SIMPLE_TIMEOUT_SECONDS=0` or native-build caching
  (`check-ui-showcase-exact-backend-matrix.shs` pattern).
- Verified 2026-09-24: TUI hello PASS, WM/GUI showcase PASS (PPM artifact),
  2D/web standalone exceed practical timeouts under available compilers.

## 5. Wiki/documentation conventions

- `doc/00_llm_process/llm_wiki.md` — compact hand-maintained entries,
  "Agent lookup rule" per entry; add when repeated ambiguity sends agents to
  the wrong subsystem.
- Expert tree: `doc/00_llm_process/feature_expert/<name>/skill.md` (copied
  from `template/feature_skill.md`); per-dir `index.md`.
- Canonical run-command guide: `doc/07_guide/ui/showcase_apps.md` (currently
  warns that graphics/web standalone are blocked by nil-receiver runtime
  failures — needs re-validation as part of this feature).

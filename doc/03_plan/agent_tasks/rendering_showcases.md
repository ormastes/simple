# Agent Task Breakdown — Rendering Showcases (parallel lanes)

Date: 2026-09-24. Design: `doc/05_design/rendering_showcases.md`. Per owner
instruction: build the shared structure first, then run each showcase as a
**parallel sidecar lane**.

## Shared interface contract (FIXED before any sidecar starts)

Sidecars must not invent or rename these:

- **Core module paths:** `examples/ui/rendering_widgets_core`,
  `examples/ui/rendering_widgets_full`, `examples/ui/rendering_2d_core`,
  `examples/ui/rendering_2d_extended`, `examples/ui/rendering_web_core`,
  `examples/ui/rendering_web_extended` (each with an `__init__.spl`).
- **Tabs data:** `rendering_tabs() -> [{id, title, tags}]` in
  `rendering_widgets_full` — the single tab definition list every lane renders.
- **Env knobs:** `SIMPLE_SHOWCASE_W/H/FRAMES`, `SHOWCASE_RESOLUTION`,
  `SIMPLE_SHOWCASE_CAPTURE` (PPM output path), `SIMPLE_GUI` (physical window),
  `SIMPLE_2D_BACKEND` (cpu|cpu_simd|vulkan|metal; **default vulkan** on lanes
  that construct an Engine2D backend — 2d and web; exact admission, honest-fail
  on unavailable backends; advisory on gui/wm headless captures),
  `SIMPLE_RENDERING_UI` (`tui|gui|web`),
  `SIMPLE_RENDERING_WEB_FIXTURE=1` (generate web fixture).
- **Entry header format (lines 2-6 of every entry):**
  `# lane: <tui|gui|wm|2d|web|webserver|switch>` and `# tier: <brief|full|core|extended>`
  plus `# core: <module path or data file>` — the census spec asserts these.
  (2026-09-24 review: `webserver` and `switch` lanes added to the enum; the
  `switch` entry's `# core:` names its data file `rendering_items.ui.sdn`.)
- **Honest-fail exit line:** `showcase status=blocked <reason>` /
  `showcase status=pass <path>` (matches existing entries).
- **Capture artifacts:** PPM + `.provenance.sdn` sidecar (wm_showcase
  convention); web writes HTML artifact.

## Lanes (sidecars run in parallel; each owns only its files)

| Lane | Owns | Notes |
|---|---|---|
| L1 tui | `app.ui_showcase.hosts.host_tui`, `rendering_tui_core/full.spl` | New char-grid ScreenHost; `(no tui)` markers for the 19 unrendered kinds |
| L2 gui | `rendering_gui_core/full.spl` + full's internal-window desktop | REQ-011: `simple_gui_internal_window` titled+borderless via `shared_wm_scene_render_to_backend` |
| L3 wm | `rendering_wm_core/full.spl` | REQ-010: HostCompositor backend, bridge admission, taskbar, sabotage+checksum gates, headless PPM default |
| L4 2d | `examples/ui/rendering_2d_core/`, `rendering_2d_extended/`, `rendering_2d_core/extended.spl` | REQ-005: shaped-text word spacing, draggable overlapping panels, hit-tested click button |
| L5 web | `examples/ui/rendering_web_core/`, `rendering_web_extended/`, `rendering_web_core/extended.spl`, fixture | REQ-006; **blocked by `_level_rank` compile defect — record bug, build structure, re-verify after fix** |
| L6 shared | `rendering_items.ui.sdn`, `rendering_switch.spl` | Item list consumed by TUI/GUI loaders + `ui web` (REQ-001, REQ-004) |
| L7 docs/gates | `doc.md`, llm_wiki entry, feature-expert skill, `showcase_apps.md` refresh, closure + capture check scripts, spec finalize | REQ-008, NFR-001/002/004; runs after L1–L6 merge |

## Merge + review

- **Merge owner:** this session (parent). Sidecars deliver on their own jj
  working-copy files; parent integrates per lane, resolves only
  cross-lane contract drift.
- **Final reviewer:** highest-capability model pass over the integrated tree —
  wiki/manifest quality, contract conformance (env knobs, headers, honest-fail
  lines), and the "no silent skip" rule for `(no tui)` / fixture / backend
  degradation.
- **Verification per lane:** `bin/simple check` on owned files (seed binary,
  `SIMPLE_TIMEOUT_SECONDS=0`); capture gates via L7 scripts. No lane may mark
  done on compile alone if a capture path exists.

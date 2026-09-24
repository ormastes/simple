# System Test Plan — Rendering Showcases

Date: 2026-09-24. Spec: `test/03_system/ui_showcase/rendering_showcases_spec.spl`.
Design: `doc/05_design/rendering_showcases.md`.

## Evidence policy (non-vacuity)

- The SPipe spec asserts **structure and wiring** (files exist with correct
  lane/tier headers, extended imports core, item-list coverage, internal-window
  API usage, WM admission API usage, theme coverage, wiki presence). These are
  the things that can be wrong without a display, and they are real string
  assertions — no `pass_todo`, no empty bodies.
- **Runtime evidence** (PPM checksums, HTTP boot probe, closure census) lives
  in `scripts/check/` per NFR-002, because graphics compiles exceed the example
  watchdog and belong in bounded check scripts, not in the spec process.
- Never claimed here: that a physical window appeared, that a browser showed
  pixels, that the WM consumed a frame headlessly beyond the scripted capture.

## Steps → requirements

| Step | Asserts | REQ |
|---|---|---|
| canonical layout census | 10 entries + items + switch + doc.md, each with `lane:`/`tier:` header | REQ-002 |
| tier split is import-based | extended/full entries import the core module path | REQ-003, NFR-001 |
| item list covers all rendering items | lane tags tui/gui/wm/2d/web, `(no tui)` markers, widget names | REQ-004 |
| gui full demonstrates internal windows | `simple_gui_internal_window`, titled + borderless chrome | REQ-011 |
| wm lane admits showcase windows | `apply_bridge_request` / `COMP_CREATE_WINDOW` / taskbar | REQ-010 |
| web theme gallery covers aqua family | `aqua_light`, `aqua_dark` + theme list | REQ-006 |
| 2d fonts/spacing/drag/click wiring | `draw_shaped_text`, pointer-event drag state, compositor hit-testing | REQ-005 |
| webserver gui serving path | `ui web` command documented + `rendering_items.ui.sdn` consumed | REQ-001 |
| wiki + guide presence | llm_wiki entry, per-dir doc.md run table | REQ-008 |

## Runtime gates (scripts/check/, owned by verify)

- `check-rendering-showcase-closure.shs` — module-closure census per tier,
  ratio ≤ 0.60 (NFR-001).
- `check-rendering-showcase-captures.shs` — headless PPM captures for
  2d/gui/wm entries (nonzero checksum + provenance), web HTML artifact
  contains all tab ids, `bin/simple ui web` bounded HTTP 200 probe.

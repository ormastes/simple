# UI Architecture

This is the entrypoint for Simple UI, GUI, web-connected UI, rendering, and UI
test architecture.

## Scope

The UI architecture owns semantic UI state, widget identity, layout intent,
event routing, accessibility state, render IR, Draw IR, shell adapters, and UI
test access. Web framework routes and persistence are separate app concerns, but
the web framework connects to UI through the `ui.web` protocol and shared UI
access snapshots.

## Stack

```text
Simple app state
  -> UI semantics: widget id, text, role, state, action names
  -> layout/style intent
  -> UI access snapshot
  -> WebRender IR / Draw IR
  -> Engine2D / backend plugin / CPU oracle
  -> shell adapter: TUI, browser, Electron, Tauri, SimpleOS WM
```

## Test And Location Model

UI tests assert both semantic state and positional/location data:

| Data | Source |
|------|--------|
| Stable identity | `canonical_id`, `surface_id`, `widget_id` |
| State | visible, focused, enabled, selected, text value |
| Position | geometry props such as `x`, `y`, `width`, `height` |
| Source/test location | SPipe spec path, generated spec doc path, scenario name |
| Pixel location | bitmap/readback coordinates and dirty regions |

Semantic assertions should use SGTTI or the shared `/api/test/*` vocabulary.
Pixel assertions should use bitmap/readback evidence. A UI test that depends on
layout must name both the semantic node and the positional property it checks.

## Ownership

| Area | Owner docs |
|------|------------|
| Stack and rendering | `simple_gui_stack.md`, `engine_2d.md`, `drawing_stack.md` |
| Semantic contract | `shared_ui_contract.md`, `ui_access_protocol.md` |
| Web transport | `ui_web_protocol.md`, `web/00_web_framework_architecture.md` |
| UI tests | `ui_test_architecture.md`, `ui_test_architecture_tldr.md` |
| dynSMF UI dependencies | `low_dependency_ui_dynsmf.md` |
| Graphics and 3D | `graphics/simple_3d_graph_ir.md`, `graphics/graphical_icon_system.md` |

## Invariants

- Simple owns UI state, event routing, layout policy, accessibility, and dirty
  region truth.
- Shells render or transport patches/input; they do not own app state.
- UI test helpers must not fork a third element model. Use `UiAccessNode`,
  `SemanticElementInfo`, or the existing `/api/test/*` element vocabulary.
- Web UI remains connected through shared UI snapshots and patch streams, not
  parallel DOM-only state.


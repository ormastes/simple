<!-- codex-research -->
# UI Access Protocol — Local Research

**Date:** 2026-04-15
**Feature:** `ui_access_protocol`
**Status:** Implemented baseline with follow-on packaging/docs

## Summary

The current project already has most of the primitives needed for an internal UI
access protocol. The missing piece was a shared semantic adapter that turns
session state, surfaces, lifecycle changes, and tool routes into one canonical
surface/node/event model.

## Existing Reuse Points

### Shared UI state

- `src/lib/common/ui/session.spl`
  - owns `UISession`, dispatch flow, mode, active tree, and named surfaces
- `src/lib/common/ui/surface.spl`
  - owns `SurfaceManager`, surface handles, active-surface tracking
- `src/lib/common/ui/widget.spl`
  - owns `UIState`, `UITree`, `WidgetNode`, widget registry queries
- `src/lib/common/ui/changelog.spl`
  - keeps session change history
- `src/lib/common/ui/lifecycle.spl`
  - computes mount/unmount/update/focus/action lifecycle diffs

### WM integration

- `src/os/services/wm/wm_service.spl`
  - window-manager service layer
- `src/os/userlib/window.spl`
  - window-facing client abstractions
- `doc/04_architecture/shared_wm_stack.md`
  - current shared WM split and ownership
- `doc/04_architecture/cross_platform_wm.md`
  - window metadata and transport constraints

### Existing test and LLM surfaces

- `src/app/ui.test_api/handler.spl`
  - additive HTTP-style UI test endpoints under `/api/test/*`
- `src/os/services/llm/mcp_os_server.spl`
  - current MCP-style OS tool surface
- `src/os/services/llm/tool_registry.spl`
  - tool schema registration and inventory
- `doc/04_architecture/shared_ui_contract.md`
  - existing stable shared UI contract for HTTP/test paths

## Current Gaps Before This Feature

1. The project had window-level and widget-level tools, but no single canonical
   snapshot spanning surfaces, nodes, and recent UI events.
2. The HTTP test API returned element/state/screenshot slices, but not a
   surface-aware semantic tree.
3. The MCP UI tooling exposed widget/window helpers, but not a stable
   protocol-oriented interface that a skill or plugin could target.
4. Session history existed, but not in a tool-facing shape scoped by
   `surface_id`.

## Constraints From Existing Implementation

### Must stay internal-only in v1

The repo already has its own `UISession` tree, synthetic widget model, and
surface manager. Reaching out to Windows UIA, AT-SPI, or macOS AX would bypass
that internal source of truth and create a second incomplete abstraction layer.
The right v1 is therefore an internal protocol over existing Simple UI
surfaces.

### Must be additive to the shared UI contract

`doc/04_architecture/shared_ui_contract.md` already defines `/api/test/*`,
protocol versioning, and error shape expectations. The new surface should add
`/api/test/ui/*` routes without breaking old consumers.

### Must reuse session/lifecycle data, not rescan from scratch

`UISession` already computes lifecycle changes and owns active-surface state.
The new protocol should materialize its output from session state and surface
manager state instead of adding a second independent tracker.

## Recommended Local Architecture

Add one shared module under `src/lib/common/ui/access.spl` that:

- derives canonical node IDs as `surface_id#widget_id`
- exports snapshot/surface/event structs
- materializes nodes from `UITree` + widget registry
- records bounded recent UI-access events
- provides renderers for JSON and text
- exposes one finder helper used by both test API and MCP tools

That module can then be consumed by:

- `UISession` for event recording and snapshot building
- `app.ui.test_api` for `/api/test/ui/*`
- `mcp_os_server` and `tool_registry` for UI-access tools
- future plugin/skill docs as the canonical workflow

## Files Touched by the Implementation

- `src/lib/common/ui/access.spl`
- `src/lib/common/ui/session.spl`
- `src/lib/common/ui/surface.spl`
- `src/lib/common/ui/__init__.spl`
- `src/app/ui.test_api/handler.spl`
- `src/app/ui.web/async_server.spl`
- `src/app/ui.tui_web/server.spl`
- `src/os/services/llm/mcp_os_server.spl`
- `src/os/services/llm/tool_registry.spl`
- `test/unit/app/ui/access_spec.spl`
- `test/unit/os/services/llm/tool_registry_spec.spl`

## Local Recommendation

Use the current `UISession` / `SurfaceManager` stack as the source of truth and
ship an additive internal UI access protocol over it. Defer external
accessibility providers and vision fallback until after the internal protocol,
skill, and plugin contract are stable.

# Audit: Shared UI Testing Surface

**Date:** 2026-04-04
**Feature:** Shared test client and protocol across web/TUI-web surfaces

## Implemented Core

Three-layer shared UI testing architecture:

**1. Shared Test Client Library** (`std.ui_test`)
- `src/lib/nogc_sync_mut/ui_test/client.spl` -- `UITestClient`: connect, click, type_text, drag, send_key, get_element, get_elements, get_state, screenshot_html, check_text, check_visible, check_focused, check_exists, wait_for, wait_ready
- `src/lib/nogc_sync_mut/ui_test/types.spl` -- `ElementInfo`, `UIStateInfo` data classes
- `src/lib/nogc_sync_mut/ui_test/http.spl` -- TCP HTTP helpers
- `src/lib/nogc_sync_mut/ui_test/parse.spl` -- JSON response parsing

**2. Shared Test API Handler** (backend-agnostic)
- `src/app/ui.test_api/handler.spl` -- `handle_test_request()` for all `/api/test/*` routes
- `src/app/ui.test_api/json.spl` -- JSON serialization

**3. Handler Integration** -- both backends use the same handler:
- `src/app/ui.web/async_server.spl:19` -- `use app.ui.test_api.handler.{handle_test_request}`
- `src/app/ui.tui_web/server.spl:16` -- `use app.ui.test_api.handler.{handle_test_request}`

## Known Limits

1. **"Shared" means web backend and tui_web proxy only** -- 11 other surfaces (ui.tui, ui.cli, ui.electron, ui.tauri, ui.browser, ui.vscode, ui.ipc, ui.mcp, ui.render, ui.none) do NOT integrate the test API
2. **HTTP-protocol-level testing only** -- does NOT test pixel rendering, layout fidelity, or platform-specific event handling
3. **Tests require compiled mode** -- tagged `slow, system`; interpreter mode only verifies file loading

## Proof References

**Test files (4 specs + 1 helper):**
- `test/system/ui/unified_test_spec.spl` -- **Key file**: starts BOTH web and tui_web servers, uses same `UITestClient` against both, compares results (3 tests)
- `test/system/ui/web_test_api_spec.spl` -- Web-only coverage (8 tests)
- `test/system/ui/tui_web_render_spec.spl` -- TUI web proxy (5 tests)
- `test/system/ui/interaction_spec.spl` -- Interaction flows (5 tests)
- `test/system/ui/helpers/ui_test_helpers.spl` -- `start_ui_server()`, `stop_ui_server()`, `free_port()`

## Recommended README Wording

> **Shared UI test client** (`std.ui_test`) -- HTTP-based test protocol with `UITestClient` for automated click/type/drag/query operations; shared `handle_test_request` handler integrated by both web backend and TUI-web proxy, with a unified spec that starts both servers and verifies equivalent behavior through the same API

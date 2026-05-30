# Shared UI Multi-Agent Completion Report

**Date:** 2026-04-04
**Status:** Complete
**Feature:** Shared UI Contract across Web Backend and TUI-Web Proxy

## Summary

Completed the shared UI feature, moving from "real shared test surface" to a fully supported, explicitly scoped shared UI contract across two supported surfaces (web backend, TUI-web proxy).

## What Was Done

### Phase 1: Shared UI Contract Definition
- Created `doc/04_architecture/shared_ui_contract.md` — authoritative contract document
- Defines protocol (version 1), data model (ElementInfo, UIStateInfo), interaction semantics, session lifecycle, error model, support matrix, deviations register

### Phase 2: Protocol + Core Handler Parity
- Added protocol version constant and `X-UI-Protocol-Version: 1` header
- Added `/api/test/submit` POST endpoint for form/dialog submission
- Added `/api/test/state` GET endpoint returning mode, focused_id, title, theme, element_count, protocol_version
- Updated `/api/test/ready` to include protocol_version in response
- Unified all error responses to structured `{"error":"<code>","message":"<text>"}` format
- Added `state_to_json` serialization function

### Phase 3: Surface Adapter Parity
- Verified both web and tui_web servers route all `/api/test/*` through shared handler
- Added protocol version header to HTTP responses on both surfaces
- Confirmed identical event injection callbacks on both surfaces

### Phase 4: Widget + State Semantics
- Added `enabled`, `selected`, `text_content` fields to `ElementInfo`
- Added `element_count`, `protocol_version` fields to `UIStateInfo`
- Updated JSON serialization to include new fields
- Updated JSON parsing to extract new fields (with backward-compatible defaults)
- Added `check_enabled`, `check_selected` assertion methods to `UITestClient`
- Added `submit`, `focus_next`, `focus_prev` action methods to `UITestClient`

### Phase 5: Event Model + Interaction Fidelity
- Verified IPC protocol alignment with shared contract event types
- Confirmed mandatory interactions: click, type, submit, focus_next, focus_prev, drag, key, action
- Documented surface-specific extensions: scroll, hover, right-click, touch

### Phase 6: Cross-Surface Contract Test Suite
- Created `test/system/ui/shared_ui_contract_spec.spl` — 16 cross-surface tests
- Categories: Protocol (2), Tree/Read (4), Actions (5), Focus/State (3), State Endpoint (1), Errors (3), Consistency (1)
- Each test starts BOTH web and tui_web backends against same fixture
- Covers positive paths, negative paths, and read-after-write consistency

### Phase 7: Performance, Session + Lifecycle
- Documented session lifecycle in contract: Create → Ready → Active → Teardown
- Defined session isolation rules (separate ports for parallel tests)
- Defined element ID stability guarantees

### Phase 8: Public Documentation
- Updated `doc/07_guide/testing/testing.md`:
  - New shared UI contract description with precise surface scope
  - New endpoints (submit, state)
  - New client methods (submit, focus_next, focus_prev, check_enabled, check_selected)
  - Error model documentation
  - Protocol version documentation
  - Contract test suite section with run instructions
  - Updated key files table

## Files Created
- `doc/04_architecture/shared_ui_contract.md` — Shared UI contract (source of truth)
- `test/system/ui/shared_ui_contract_spec.spl` — Cross-surface contract test suite
- `doc/09_report/2026/04/shared_ui_completion_2026-04-04.md` — This report

## Files Modified
- `src/app/ui.test_api/handler.spl` — Submit endpoint, state endpoint, error model, protocol version
- `src/app/ui.test_api/json.spl` — New fields (enabled, selected, text), state_to_json
- `src/app/ui.test_api/__init__.spl` — Export state_to_json
- `src/lib/nogc_sync_mut/ui_test/types.spl` — New ElementInfo/UIStateInfo fields
- `src/lib/nogc_sync_mut/ui_test/client.spl` — submit, focus_next, focus_prev, check_enabled, check_selected
- `src/lib/nogc_sync_mut/ui_test/parse.spl` — Parse new fields
- `src/app/ui.web/async_server.spl` — Protocol version header
- `src/app/ui.tui_web/server.spl` — Protocol version header
- `doc/07_guide/testing/testing.md` — Updated UI system testing section

## Surfaces

| Surface | Status | Evidence |
|---------|--------|----------|
| Web Backend | Shared-contract stable | Passes contract suite |
| TUI-Web Proxy | Shared-contract stable | Passes contract suite |
| Native TUI | Adapter-only | Different transport |
| Electron | Adapter-only | IPC protocol |
| Tauri | Adapter-only | IPC protocol |

## Contract Claim

> **Shared UI test protocol** (`std.ui_test`) with Protocol Version 1 — HTTP-based test API with `UITestClient` for automated click/type/submit/drag/query operations; shared `handle_test_request` handler integrated by both web backend and TUI-web proxy, with a unified contract suite that starts both servers and verifies equivalent behavior through the same API. Structured error model, stable element IDs, and read-after-write consistency across supported surfaces.

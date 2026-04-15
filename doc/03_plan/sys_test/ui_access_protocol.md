<!-- codex-design -->
# UI Access Protocol — System Test Plan

**Feature:** `ui_access_protocol`
**Date:** 2026-04-15

## Coverage Goal

Prove that the internal UI access protocol provides a stable additive semantic
surface for session trees, test routes, and MCP tooling without breaking the
legacy widget paths.

## Test Cases

### Snapshot generation

- create a session with a main tree
- verify snapshot contains protocol version, active surface, and canonical IDs

### Multi-surface behavior

- open a second named surface
- verify snapshot returns both surfaces
- verify active-surface changes are reflected

### Find

- search by kind
- search by text
- search by surface filter
- search by focused-only flag

### History

- dispatch actions and update a surface tree
- verify recent events are recorded
- verify surface-scoped history filtering works
- attach a store, restart the runtime, and verify persisted history survives
- verify persisted node search survives restart with the same database

### Window metadata registry

- bind a window to a surface through the shared runtime registry
- verify `window_id` and `app_id` are visible in snapshot and surface reads
- verify persisted snapshots do not store runtime `window_id` handles

### HTTP route compatibility

- call `/api/test/ui/snapshot`
- call `/api/test/ui/surface`
- call `/api/test/ui/history`
- call `/api/test/ui/act`
- call `/api/test/ui/observe`
- call `GET /api/test/ui/state`
- call `POST /api/test/ui/state`
- verify old `/api/test/element` and `/api/test/elements` still work

### MCP schema/dispatch

- verify tool registry includes the seven UI access tools
- verify schema fields match tool dispatch expectations
- verify declarative `observe` and `state` preserve canonical IDs while
  resolving through the same snapshot/action paths
- verify MCP reads use persisted history/search when available
- verify MCP snapshot window metadata matches the shared registry

### Runtime config

- verify explicit DB-path override wins over env/default resolution
- verify disable values (`0`, `false`, `off`) skip auto-attachment

## Manual Verification

- run a UI app with multiple surfaces
- inspect `ui_access_snapshot`
- inspect `ui_access_observe`
- inspect `ui_access_state`
- trigger an action via `ui_access_act`
- trigger the same action via declarative `state`
- inspect `ui_access_history`
- restart the same runtime with the same UI access DB and verify history reuse
- confirm `screenshot` now reflects the canonical access tree text

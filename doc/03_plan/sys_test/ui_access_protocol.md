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

### HTTP route compatibility

- call `/api/test/ui/snapshot`
- call `/api/test/ui/surface`
- call `/api/test/ui/history`
- call `/api/test/ui/act`
- verify old `/api/test/element` and `/api/test/elements` still work

### MCP schema/dispatch

- verify tool registry includes the five new UI access tools
- verify schema fields match tool dispatch expectations

## Manual Verification

- run a UI app with multiple surfaces
- inspect `ui_access_snapshot`
- trigger an action via `ui_access_act`
- inspect `ui_access_history`
- confirm `screenshot` now reflects the canonical access tree text

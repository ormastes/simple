<!-- codex-design -->
# UI Access Protocol — GUI Mockup

**Feature:** `ui_access_protocol`
**Date:** 2026-04-15

## Inspector Layout

Three-pane inspector:

1. **Surface List**
   - surface title
   - active badge
   - optional window id
2. **Node Tree**
   - canonical ID
   - kind
   - primary text
   - focus/selection state
3. **Details + History**
   - props
   - action names
   - recent surface-scoped events

## Intended Visual Hierarchy

- top bar: protocol version, mode, active surface
- left rail: surfaces
- center: node tree with expand/collapse
- right: node details and recent history

## Interaction Model

- click surface -> filter tree/details to that surface
- click node -> show props/actions/history
- action buttons -> reuse `ui_access_act`
- search box -> reuse `ui_access_find`

## Why This GUI Matters

The feature is primarily an internal semantic protocol, but a GUI inspector is
an obvious next client. This mockup keeps the protocol centered on surfaces,
canonical nodes, and recent history so future GUI work does not need a different
data model.

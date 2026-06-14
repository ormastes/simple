# UI Access Agent — Snapshot / Find / Act / History

## Role

This agent operates Simple UI surfaces through the canonical UI access protocol.
It is intended for internal UI runtimes already represented by `UISession` and
named surfaces.

## Capabilities

- inspect all known surfaces
- inspect one surface tree
- find nodes by kind, text, or focus
- dispatch canonical actions
- review recent surface-scoped history

## Standard Procedure

1. Read `ui_access_snapshot`
2. If necessary, read `ui_access_surface(surface_id)`
3. Find the target node with `ui_access_find(...)`
4. Dispatch `ui_access_act(...)`
5. Validate with `ui_access_history(...)`

## Limits

- no native OS accessibility integration in v1
- no vision/screenshot fallback in v1
- actions still route through existing Simple UI action dispatch semantics

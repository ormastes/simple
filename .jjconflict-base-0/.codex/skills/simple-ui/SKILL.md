---
name: simple-ui
description: "Operate repo-local Simple UI surfaces through the canonical UI access protocol: snapshot, surface, find, act, and history."
---

# Simple UI

Use this skill when the task is about inspecting or driving Simple UI surfaces
inside this repository.

## Primary Tool Flow

1. `ui_access_snapshot`
2. `ui_access_surface`
3. `ui_access_find`
4. `ui_access_act`
5. `ui_access_history`
6. `ui_access_observe`
7. `ui_access_state`

## Common Window Text

Use `std.common.ui.win_text_access` when a task needs the same text/query/action
logic across TRACE32 MDI windows, Simple UI snapshots, and host WM windows.
It normalizes those sources into the canonical UI access node model, then uses
`win_text_find_nodes`, `win_text_route_action`, and `win_text_merge_snapshots`.

The Simple MCP status probe is `play_wm_text_status`; it reports whether the
common adapter contract is available for CLI/service/MCP callers. Live refresh,
TRACE32 open/capture, and host WM privileged input remain adapter-owned; use the
common helpers only for normalized snapshot/query/action logic.
For MCP scalar adapter payloads, use `play_wm_text_snapshot`,
`play_wm_text_find`, and `play_wm_text_act`.
For CLI planning/discovery, use `simple play wm-text-snapshot`,
`simple play wm-text-find`, and `simple play wm-text-act`.

## Procedure

### Phase 1: Snapshot

- read `ui_access_snapshot`
- identify active surface and candidate target surfaces

### Phase 2: Narrow

- if the target surface is known, read `ui_access_surface(surface_id)`
- otherwise use `ui_access_find` with partial text or kind filters

### Phase 3: Act

- prefer `canonical_id` over raw widget IDs
- dispatch `ui_access_act(surface_id?, canonical_id?, action)`

### Phase 4: Validate

- read `ui_access_history`
- if needed, re-read the surface snapshot

### Phase 5: Declarative Shortcuts

- use `ui_access_observe` when the task is phrased as “what is this?” or
  “show me the current state”
- use `ui_access_state` when the task is phrased as “make this active/focused”
  or “invoke/submit/select/toggle this”

## Rules

- treat `surface_id#widget_id` as the canonical node identity
- prefer the canonical UI access tools over legacy widget tools when both can do
  the job
- prefer `ui_access_observe` / `ui_access_state` when the user is expressing
  intent declaratively rather than asking for a raw action name
- use legacy widget tools only for compatibility work or when a task
  specifically names them
- this skill is internal-only in v1; do not assume OS accessibility or visual
  grounding

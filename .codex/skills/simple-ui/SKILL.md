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

## Rules

- treat `surface_id#widget_id` as the canonical node identity
- prefer the canonical UI access tools over legacy widget tools when both can do
  the job
- use legacy widget tools only for compatibility work or when a task
  specifically names them
- this skill is internal-only in v1; do not assume OS accessibility or visual
  grounding

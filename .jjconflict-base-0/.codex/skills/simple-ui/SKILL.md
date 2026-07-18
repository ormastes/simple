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

## Deployed CLI Flow

Use the same access order through the deployed CLI:

1. `simple ui windows`
2. `simple ui snapshot` or `simple ui surface <surface_id>`
3. `simple ui find --surface <surface_id> ...`
4. `simple ui act --canonical <surface_id#widget_id> --action <action>`
5. `simple ui history --surface <surface_id>`

Human output is the default; add `--json` for one machine-readable
`simple.access/v1` envelope. Live commands use the existing loopback UI test
API (and accept `--port N`). `--ui-access-db PATH` is an explicit read-only
fallback for list/snapshot/surface/find/history; it rejects `act` rather than
turning the store into a command queue.

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
For live host-WM CLI access, use `simple play windows`,
`simple play wm-text-snapshot host_wm`,
`simple play wm-text-find host_wm <text>`,
`simple play wm-text-act <canonical_id> <action>`, and
`simple play wm-text-history`.

## SPipe GUI Test Know-How

GUI SPipe tests should verify behavior through the actual access surface when
available, not just through screenshots. Use snapshot/find/action/history or the
`wm-text-*` adapters to open a surface, locate the target by visible text or
role, perform the interaction, and assert the post-action surface state. Keep
screenshots as visual evidence for layout, theme, and pixel regressions.

For MDI/window-manager work, also prove event propagation when practical:
assert the dispatch action/target, local coordinates, focus or drag state,
stale event-cache rejection after layout movement, and any Draw IR event target
handoff (`DrawIrEventTargetContext`) if rendering or backend routing changed.
When the renderer/backend architecture changes, distinguish drawing backend
evidence from processing/offload backend evidence.

## Canonical Showcase Manual Flow

Use these stable app IDs across every supported launch surface:

| App ID | Purpose |
|---|---|
| `graphics_2d_showcase` | 2D primitive and text rendering |
| `web_standards_showcase` | HTML/CSS/web standards rendering |
| `gui_widget_showcase` | Widget state and interaction |

Run each applicable app on `standalone`, `host_wm`, and `simpleos_wm`. For each
combination: snapshot the surface, find the app by canonical ID or visible role,
act on at least one semantic control, read history, then snapshot again. Assert
the action target and resulting semantic state. Also require a nonblank frame
and drawing/processing backend provenance from the same run.

Evidence fails if it uses a dummy or blank frame, source-text assertions alone,
synthetic handles presented as real backend handles, or an action log without a
post-action semantic-state change. Screenshots supplement these checks; they do
not replace snapshot/find/act/history or framebuffer/provenance evidence.

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

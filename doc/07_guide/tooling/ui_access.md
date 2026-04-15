# UI Access Guide

`ui_access` is the canonical semantic inspection and control surface for Simple
UI sessions. It exposes one stable model across named surfaces, HTTP test
routes, MCP tools, and agent skills.

This is an internal Simple UI protocol in v1. It is not OS accessibility and it
is not a general desktop automation layer.

Runtime note:

- session-owning startup paths such as `simple ui web`, CLI observer mode,
  headless mode, and bridge-based MCP usage now auto-attach a file-backed
  `UiAccessStore`
- set `SIMPLE_UI_ACCESS_DB_PATH=/path/to/ui_access.sqlite` to force the store
  location
- set `SIMPLE_UI_ACCESS_DB_PATH=0` to disable runtime store attachment

---

## What It Exposes

The canonical snapshot contains:

- `protocol_version`
- `mode`
- `active_surface`
- `surfaces`
- `nodes`
- `recent_events`

Each node uses a stable canonical identity:

```text
surface_id#widget_id
```

Examples:

- `main#submit_btn`
- `popup#ok_btn`

---

## Primary Workflow

Use the protocol in this order:

1. `ui_access_snapshot`
2. `ui_access_surface`
3. `ui_access_find`
4. `ui_access_act`
5. `ui_access_history`

This matches the repo-local agent skill at [.codex/skills/simple-ui/SKILL.md](../../../.codex/skills/simple-ui/SKILL.md).

---

## MCP Tools

The MCP OS server exposes five tools:

| Tool | Purpose | Result shape |
|------|---------|--------------|
| `ui_access_snapshot` | Read the canonical snapshot across all surfaces | JSON |
| `ui_access_surface` | Read one named surface and its nodes | JSON |
| `ui_access_find` | Find nodes by surface, kind, text, or focus | Text |
| `ui_access_act` | Dispatch an action to a surface or canonical node | Text |
| `ui_access_history` | Read recent access events globally or per surface | JSON |

Important behavior:

- `ui_access_find` returns a text summary, not JSON.
- `ui_access_act` returns a short dispatch result such as
  `ok: dispatched click_ok_btn`.
- `ui_access_act` switches the active surface before dispatch when the target
  surface is known.

---

## HTTP Test Routes

The shared test API exposes additive routes under `/api/test/ui/*`:

| Route | Method | Purpose |
|------|--------|---------|
| `/api/test/ui/snapshot` | `GET` | Canonical snapshot |
| `/api/test/ui/surface?id=<surface_id>` | `GET` | One surface and its nodes |
| `/api/test/ui/history?surface_id=<id>&count=<n>` | `GET` | Recent events |
| `/api/test/ui/act` | `POST` | Action dispatch |

Example action body:

```json
{
  "surface_id": "popup",
  "canonical_id": "popup#ok_btn",
  "action": "click"
}
```

Compatibility rules:

- Existing `/api/test/state`, `/api/test/element`, `/api/test/elements`, and
  `/api/test/screenshot` routes remain available.
- If no live `UISession` exists, snapshot falls back to the current `UIState`
  tree and history returns `[]`.

---

## Find Semantics

`ui_access_find` prefers the attached `UiAccessStore` current-node index when a
store is present. If no store is attached, it falls back to filtering the live
in-memory snapshot.

Matching behavior:

- `surface_id` filters to one named surface when provided
- `kind` is case-insensitive
- `text` performs substring matching across widget id, visible text, and node
  props
- `focused_only=true` limits results to currently focused nodes

---

## Action Semantics

Prefer canonical IDs over raw widget IDs.

The action resolver accepts semantic aliases and maps them to the session’s
legacy action names when needed. Common forms:

- `click`
- `invoke`
- `press`
- `activate`
- `focus`
- `toggle`
- `submit`
- `select`

If the action already targets a widget, such as `click_ok_btn`, it is preserved
as-is.

---

## History Semantics

History is a bounded event view intended for debugging and agent confirmation.

Behavior:

- if a `UiAccessStore` is attached to the session, `ui_access_history` and
  `/api/test/ui/history` read persisted events first
- if no store is attached, they fall back to the in-memory recent event list
- the store also keeps a latest-node table used by persisted `ui_access_find`
  reads

Use it to answer:

- which surface became active
- which action was dispatched
- whether a route or MCP call actually changed the session

Do not treat the default session history as an audit log. For durable reads,
attach a `UiAccessStore` to the session.

---

## Typical Operator Flow

### Read the current surfaces

```text
ui_access_snapshot
```

### Narrow to one surface

```text
ui_access_surface("popup")
```

### Find a button by text

```text
ui_access_find(surface_id="popup", kind="button", text="OK", focused_only="false")
```

### Dispatch an action

```text
ui_access_act(surface_id="popup", canonical_id="popup#ok_btn", action="click")
```

### Confirm the result

```text
ui_access_history(surface_id="popup", count="10")
```

---

## Current Verification Coverage

The protocol is covered in:

- [test/unit/app/ui/access_spec.spl](../../../test/unit/app/ui/access_spec.spl)
- [test/unit/app/ui/ui_access_http_spec.spl](../../../test/unit/app/ui/ui_access_http_spec.spl)
- [test/unit/os/services/llm/ui_access_dispatch_spec.spl](../../../test/unit/os/services/llm/ui_access_dispatch_spec.spl)
- [test/system/ui/ui_access_contract_spec.spl](../../../test/system/ui/ui_access_contract_spec.spl)
- [doc/06_spec/app/os/feature/ui_access_protocol_spec.spl](../../06_spec/app/os/feature/ui_access_protocol_spec.spl)

Current limitation:

- the route and dispatch coverage is strong, but there is not yet a dedicated
  large-tree performance benchmark for snapshot generation or `ui_access_find`.

---

## See Also

- [tooling/mcp.md](mcp.md)
- [ui_stack_guide.md](../ui_stack_guide.md)
- [requirements](../../02_requirements/feature/ui_access_protocol.md)
- [architecture](../../04_architecture/ui_access_protocol.md)

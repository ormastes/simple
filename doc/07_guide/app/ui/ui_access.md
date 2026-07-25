# UI Access Guide

`ui_access` is the canonical semantic inspection and control surface for Simple
UI sessions. It exposes one stable model across named surfaces, HTTP test
routes, MCP tools, and agent skills.

This is an internal Simple UI protocol in v1. It is not OS accessibility and it
is not a general desktop automation layer.

Runtime note:

- session-owning startup paths such as `simple ui web`, `simple ui tui_web`,
  `simple ui browser`, CLI observer mode, headless mode, and bridge-based MCP
  usage now auto-attach a file-backed `UiAccessStore`
- pass `--ui-access-db /path/to/ui_access.sqlite` to override the runtime store
  path explicitly; this takes precedence over the environment
- set `SIMPLE_UI_ACCESS_DB_PATH=/path/to/ui_access.sqlite` to force the store
  location
- set `SIMPLE_UI_ACCESS_DB_PATH=0` to disable runtime store attachment

The live transport gate covers both the web fixture and the canonical TUI-web
backend as separate server processes. Both are inspected through the same
`simple ui windows|snapshot|surface|find|act|history` client protocol; retained
TUI-web evidence is written to `protocol/tui-web.json`. Acceptance runs on the
Pure-Simple self-hosted `bin/simple`; the Rust compiler is bootstrap seed only
and is rejected as UI-access evidence.

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

Typed value access is additive and applies only to canonical `input`,
`textfield`, and `textarea` nodes.

---

## Primary Workflow

Use the protocol in this order:

1. `ui_access_snapshot`
2. `ui_access_surface`
3. `ui_access_find`
4. `ui_access_act`
5. `ui_access_history`

Declarative shortcuts and typed value access now sit on top of that base flow:

6. `ui_access_observe`
7. `ui_access_state`
8. `ui_access_query`
9. `ui_access_ensure`
10. `ui_access_value`
11. `ui_access_adapter_snapshot`
12. `ui_access_visual_probe`

This matches the repo-local agent skill at [.codex/skills/simple-ui/SKILL.md](../../../.codex/skills/simple-ui/SKILL.md).

---

## Common Window Text Access

`std.common.ui.win_text_access` extends the canonical UI access model to
non-Simple window sources. This unified contract is called the **Simple Gui
Texture Tree Interface (SGTTI)** — see the glossary entry for full context. It
currently normalizes four sources:

- **TRACE32** text or MDI windows captured by catalog/open/capture metadata
- **Simple UI** access snapshots (in-process semantic)
- **Host WM** top-level windows (Linux/macOS/Windows)
- **SimpleOS Compositor** surfaces via the SGTTI adapter (`src/os/compositor/gtti.spl`)

The compositor source bridges `Compositor` surfaces into access nodes, including
in **hidden WM mode** (`WM_MODE_HIDDEN`) where the compositor populates its
surface tree without rendering to a display backend — enabling headless GUI
testing. Use `gtti_snapshot_from_compositor(comp, WM_MODE_HIDDEN, ...)` to
snapshot compositor state.

The shared layer provides snapshot construction, staleness metadata, filtered
text lookup, snapshot merging, and action routing through
`win_text_find_nodes`, `win_text_route_action`, and `win_text_merge_snapshots`.
Backends still own live refresh and privileged input; the common module keeps
the query/action contract consistent across CLI, service, and MCP callers.

The Simple MCP probe `play_wm_text_status` reports whether the common adapter
contract is available. It is intentionally a status/contract probe, not a live
refresh command; adapters still own their backend-specific refresh and
privileged input steps.

MCP clients that already have scalar adapter data can call the common facade
directly:

| Tool | Purpose |
|------|---------|
| `play_wm_text_snapshot` | SGTTI snapshot — normalize TRACE32, Simple UI, host WM, or compositor payload |
| `play_wm_text_find` | SGTTI query — find nodes in the normalized texture tree |
| `play_wm_text_act` | SGTTI action — validate and route against a normalized canonical target |

Pass `"source": "compositor"` to `play_wm_text_snapshot` to build a compositor
snapshot with optional `wm_mode`, `window_id`, `title`, `width`, `height`,
`visible`, `focused`, and `app_id` fields.

These tools do not refresh live backends. For live Simple UI sessions, use
`ui_access_*`; for live TRACE32 open/capture, use TRACE32 MCP tools first and
then pass captured text to the common facade.

The startup-light play CLI recognizes matching planner subcommands:
`simple play wm-text-snapshot`, `simple play wm-text-find`, and
`simple play wm-text-act`.

## SPipe Test API Consistency

Executable UI, SGTTI, and Draw IR specs should use the canonical SPipe import:

```simple
use std.spec
```

`std.spipe` is a compatibility alias for existing specs. Keep UI-specific
helpers such as SGTTI query/action checks or future `expect_draw` assertions as
helper calls inside normal `describe`/`it` scenarios; do not create a parallel
test framework or replace the built-in SPipe matchers.

For in-process SGTTI tests, use `SgttiTestDriver` over a `WinTextSnapshot`.
Use `SgttiTestDriver.from_tui_state` or `sgtti_snapshot_from_tui_state` when a
TUI `UIState` should be asserted through the shared SGTTI surface. Use
`gui_test_snapshot` or `gui_test_snapshot_default` when a headless compositor
window should be asserted through the same driver without copying compositor
fixture setup. Select surfaces with `UI_TEST_TARGET_TUI`, `UI_TEST_TARGET_GUI`,
`UI_TEST_TARGET_BOTH`, and `ui_test_targets`; use `sgtti_parity_check` when a
`both` run must prove visible/focused/enabled/selected state agrees across TUI
and GUI snapshots.
Use `sgtti_snapshot_from_draw_ir_batch` or
`sgtti_snapshot_from_draw_ir_composition` when an Engine2D/Web Draw IR scene
must assert semantic node structure before raster/pixel readback.

Protocol v2 Draw IR inspection is optional and capability-gated. Use
`/api/test/draw-ir`, `/api/test/draw-ir?id=...`,
`/api/test/draw-ir/diff`, and `/api/test/draw-ir/layout?id=...` for Draw IR
surfaces; use `/api/test/draw-ir/diff?baseline=...` for baseline-to-current
geometry/style/color/text-bound comparisons. Keep Protocol v1 element/state/
action endpoints stable. The typed model is `DrawIrComposition`; SDN
interchange is provided by `src/lib/common/ui/draw_ir_sdn.spl`, and Draw.io
mxGraph interchange by `src/lib/common/ui/draw_ir_drawio.spl`.
For GUI tests that need to know what was rendered where, call
`/api/test/draw-ir/layout?id=...&capability=draw_ir` or use `expect_draw` to
assert stable id, kind/role, geometry, hit rect, parent, and computed style
inside a normal SPipe scenario before using screenshots as supplemental
evidence.

---

## MCP Tools

The MCP OS server exposes twelve tools:

| Tool | Purpose | Result shape |
|------|---------|--------------|
| `ui_access_snapshot` | Read the canonical snapshot across all surfaces | JSON |
| `ui_access_surface` | Read one named surface and its nodes | JSON |
| `ui_access_find` | Find nodes by surface, kind, text, or focus | Text |
| `ui_access_act` | Dispatch an action to a surface or canonical node | Text |
| `ui_access_history` | Read recent access events globally or per surface | JSON |
| `ui_access_observe` | Declaratively observe a node, surface, or filtered query | JSON or text |
| `ui_access_state` | Read or set declarative state for a surface or node | JSON or text |
| `ui_access_value` | Read or write typed values for canonical `input`, `textfield`, and `textarea` nodes | JSON or text |
| `ui_access_query` | Query canonical nodes with structured JSON results | JSON |
| `ui_access_ensure` | Ensure a bounded declarative expectation over canonical query results | JSON |
| `ui_access_adapter_snapshot` | Wrap a canonical snapshot in additive source/target metadata | JSON |
| `ui_access_visual_probe` | Read semantic marks and issues for a surface from the vision sidecar | JSON |

Important behavior:

- `ui_access_find` returns a text summary, not JSON.
- `ui_access_act` returns a short dispatch result such as
  `ok: dispatched click_ok_btn`.
- `ui_access_act` switches the active surface before dispatch when the target
  surface is known.
- `ui_access_observe` chooses the narrowest read automatically:
  canonical node -> filtered snapshot JSON, surface -> surface JSON, query ->
  `ui_access_find` text, no selector -> full snapshot JSON.
- `ui_access_state` reads current state when no `state_key` is supplied, and
  supports constrained declarative writes for `active`, `focused`, `invoke`,
  `submit`, `select`, `toggle`, and `action`.
- `ui_access_value` is the typed form-value layer. Use it for `input`,
  `textfield`, and `textarea` nodes when you need the node's value rather than
  generic state; it is additive over snapshot/query/state/ensure flows.
- `ui_access_query` keeps filtered reads in JSON form with `query`,
  `match_count`, `truncated`, `surfaces`, and `nodes`.
- `ui_access_ensure` reuses the same selector space as `query`, then evaluates
  one bounded expectation such as `exists`, `absent`, `focused`, `enabled`, or
  `match_count`.
- `ui_access_adapter_snapshot` is additive metadata around the same canonical
  snapshot, not a second snapshot model.
- `ui_access_visual_probe` currently projects semantic marks from canonical
  nodes and reports structured issues when no pixel provider is configured.

---

## HTTP Test Routes

The shared test API exposes additive routes under `/api/test/ui/*`:

| Route | Method | Purpose |
|------|--------|---------|
| `/api/test/ui/snapshot` | `GET` | Canonical snapshot |
| `/api/test/ui/surface?id=<surface_id>` | `GET` | One surface and its nodes |
| `/api/test/ui/history?surface_id=<id>&count=<n>` | `GET` | Recent events |
| `/api/test/ui/act` | `POST` | Action dispatch |
| `/api/test/ui/observe?...` | `GET` | Declaratively observe a node, surface, or filtered query |
| `/api/test/ui/state?...` | `GET` | Read declarative state for a surface or node |
| `/api/test/ui/state` | `POST` | Set constrained declarative state for a surface or node |
| `/api/test/ui/value?canonical_id=<id>` | `GET` | Read the typed value for a canonical input/textfield/textarea node |
| `/api/test/ui/value` | `POST` | Write the typed value for a canonical input/textfield/textarea node |
| `/api/test/ui/query?...` | `GET` | Query canonical nodes with structured JSON results |
| `/api/test/ui/ensure?...` | `GET` | Ensure a bounded declarative expectation over canonical query results |
| `/api/test/ui/adapter_snapshot?...` | `GET` | Read additive source/target metadata around a canonical snapshot |
| `/api/test/ui/visual_probe?...` | `GET` | Read semantic marks and issues from the vision sidecar |

Example action body:

```json
{
  "surface_id": "popup",
  "canonical_id": "popup#ok_btn",
  "action": "click",
  "expected_revision": 42
}
```

CLI actions always send `expected_revision` from the observed snapshot. Direct
API clients should do the same; a mismatch returns `stale_target` before dispatch.

Compatibility rules:

- Existing `/api/test/state`, `/api/test/element`, `/api/test/elements`, and
  `/api/test/screenshot` routes remain available.
- If no live `UISession` exists, snapshot falls back to the current `UIState`
  tree and history returns `[]`.
- `GET /api/test/ui/observe` requires at least one selector:
  `surface_id`, `canonical_id`, `kind`, `text`, or `focused_only`.
- `GET /api/test/ui/query` accepts the same selectors as `observe`, plus
  optional `limit`.
- `GET /api/test/ui/ensure` accepts the same selectors as `query`, plus
  `expectation`, optional `expected_value`, and optional bounded wait controls
  `timeout_ms` and `poll_ms`.
- `POST /api/test/ui/state` requires `state_key` and either `surface_id` or
  `canonical_id`.

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

### Observe declaratively

```text
ui_access_observe(canonical_id="popup#ok_btn")
```

### Set declarative state

```text
ui_access_state(canonical_id="main#submit_btn", state_key="invoke", state_value="true")
```

### Read or write a typed value

```text
ui_access_value(canonical_id="main#search_input")
ui_access_value(surface_id="main", canonical_id="main#search_input", value="typed query")
```

### Query structured matches

```text
ui_access_query(surface_id="popup", kind="button", text="OK", focused_only="false", limit="10")
```

### Ensure a goal state

```text
ui_access_ensure(surface_id="popup", kind="button", focused_only="true", expectation="match_count", expected_value="1", limit="1")
```

### Confirm the result through history

```text
ui_access_history(surface_id="popup", count="10")
```

---

## Current Verification Coverage

The protocol is covered in:

- [test/01_unit/app/ui/access_spec.spl](../../../test/01_unit/app/ui/access_spec.spl)
- [test/01_unit/app/ui/ui_access_http_spec.spl](../../../test/01_unit/app/ui/ui_access_http_spec.spl)
- [test/01_unit/os/services/llm/ui_access_dispatch_spec.spl](../../../test/01_unit/os/services/llm/ui_access_dispatch_spec.spl)
- [test/03_system/ui/ui_access_contract_spec.spl](../../../test/03_system/ui/ui_access_contract_spec.spl)
- [test/03_system/app/os/feature/ui_access_protocol_spec.spl](../../../test/03_system/app/os/feature/ui_access_protocol_spec.spl)
- [test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl](../../../test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl)

Current limitation:

- the route and dispatch coverage is strong, but there is not yet a dedicated
  large-tree performance benchmark for snapshot generation or `ui_access_find`.

---

## See Also

- [tooling/mcp.md](mcp.md)
- [ui_stack_guide.md](../ui_stack_guide.md)
- [requirements](../../02_requirements/feature/ui_access_protocol.md)
- [architecture](../../04_architecture/ui_access_protocol.md)
- [WM text-access requirements](../../02_requirements/feature/wm_text_access_mcp.md)
- [WM text-access architecture](../../04_architecture/wm_text_access_mcp.md)

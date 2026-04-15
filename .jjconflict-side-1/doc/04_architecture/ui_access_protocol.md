<!-- codex-design -->
# UI Access Protocol — Architecture

**Feature:** `ui_access_protocol`
**Date:** 2026-04-15
**Status:** Implemented v1 architecture

## Goal

Provide one internal semantic UI protocol that all repo-local test, MCP, skill,
and plugin flows can target without re-deriving UI state in different ways.
The protocol is additive: snapshot, query, state, ensure, and value layers all
hang off the same canonical node model, with adapter-envelope and vision-sidecar
reads layered on the same surface identity.

## Architecture Decision

Use an internal shared access adapter over `UISession` and `SurfaceManager`.

- Source of truth:
  - `UISession`
  - `SurfaceManager`
  - `UITree` / widget registry
  - WM metadata already owned by the OS service
- Serving surfaces:
  - `/api/test/ui/*`
  - MCP UI-access tools
  - derived text/markdown tree renderers
  - plugin/skill documentation

Do not integrate native UIA/AT-SPI/AX in v1.

## Layering

### Common UI layer

`src/lib/common/ui/access.spl`

Owns:

- `UiAccessNode`
- `UiAccessSurface`
- `UiAccessEvent`
- `UiAccessSnapshot`
- typed value helpers for `input`, `textfield`, and `textarea` nodes
- additive source/adapter envelope types
- additive vision-sidecar types and semantic mark projection
- canonical ID rules
- snapshot builders
- event list helpers
- finder helpers
- JSON/text rendering

This is the canonical protocol module.

### Session layer

`src/lib/common/ui/session.spl`

Owns:

- recording recent UI access events
- exposing snapshot/history helpers
- attaching and querying the optional `UiAccessStore`
- exposing shared window-surface registry bindings
- bridging lifecycle changes into canonical access events
- preserving active-surface semantics

### Test API layer

`src/app/ui.test_api/handler.spl`

Owns additive HTTP contract routes:

- `GET /api/test/ui/snapshot`
- `GET /api/test/ui/surface?id=...`
- `GET /api/test/ui/history?...`
- `POST /api/test/ui/act`
- `GET /api/test/ui/observe?...`
- `GET /api/test/ui/state?...`
- `POST /api/test/ui/state`

The existing `/api/test/*` contract remains valid.

### MCP OS tool layer

`src/os/services/llm/mcp_os_server.spl`
`src/os/services/llm/tool_registry.spl`

Own:

- LLM-facing tool registration
- routing reads through persisted access data when available
- canonical action dispatch
- additive `ui_access_value` typed value read/write dispatch
- additive `ui_access_adapter_snapshot` envelope dispatch
- additive `ui_access_visual_probe` sidecar dispatch
- declarative observe/state shims over the canonical snapshot/action paths
- snapshot-derived text rendering

## Canonical Data Model

### Node identity

`canonical_id = surface_id + "#" + widget_id`

Rationale:

- stable within the current UI runtime
- readable in logs and prompts
- easy to split back into surface/widget parts

### Surface model

Each surface carries:

- `surface_id`
- `title`
- `active`
- `window_id`
- `app_id`
- `root_canonical_id`

Window metadata is enrichment, not the primary identity source.
Runtime `window_id` values are resolved through the shared window-surface
registry and are intentionally stripped from persisted snapshots.

### Value model

Typed value access applies only to canonical nodes whose kinds are `input`,
`textfield`, or `textarea`.

- reads return the node's typed value from the live canonical snapshot/session
- writes update the same canonical node value and refresh through the existing
  session render path
- all other node kinds are rejected explicitly

### Event model

Recent access events are bounded, append-only in memory, and surface-scoped.
When a `UiAccessStore` is attached, the same canonical events are also persisted
and can be queried across runtime restarts.

## Hot Paths

### Snapshot read

1. read current session state and surface inventory
2. collect node metadata from in-memory trees/widget registry
3. enrich surfaces from the shared runtime window-surface registry
4. serialize to JSON or text

### Find

1. query the attached access-store index when available
2. otherwise build or fetch the current snapshot
3. filter nodes by surface/kind/text/focus
4. render filtered text or JSON response

### History

1. query persisted access events when a store is attached
2. otherwise read bounded in-memory recent events from the session
3. scope by `surface_id` when requested
4. serialize as canonical JSON events

### Action

1. resolve surface and optional canonical node
2. set active surface
3. dispatch an existing `UIEvent.Action`
4. render/refresh

### Value

1. resolve surface and canonical node
2. verify the node kind is value-bearing
3. read or update the typed value on the live canonical node
4. render/refresh after writes

### Adapter snapshot

1. resolve the current canonical surface snapshot
2. derive source metadata from the active live session/surface
3. wrap the canonical snapshot in an additive adapter envelope
4. preserve a usable null-adapter default so the route/tool stays additive

### Visual probe

1. resolve the current canonical snapshot for the selected surface
2. project canonical nodes into semantic bounds/mark records
3. return structured issues when no image-backed capture provider is configured
4. keep the sidecar read-only and non-blocking

## Cache and Invalidation Strategy

- current snapshots are still rebuilt from live in-memory session/surface state
- the optional `UiAccessStore` maintains a persisted current-node view plus
  append-only events for read paths that need restart durability
- runtime window bindings live only in the shared in-memory registry and are
  rebuilt on startup
- writes flow from session updates into the store; read paths prefer the store
  when attached and otherwise fall back to live in-memory state
- typed value reads/writes reuse the live session state and the same refresh
  path as other canonical UI updates; they do not introduce a separate value
  cache

## Risks

### Legacy action naming

The current system still dispatches through action-name strings such as
`click_widgetId`. The protocol wraps that behavior but does not replace it in
v1.

### Runtime-only window handles

Window IDs and native handles are not durable identity. The architecture avoids
persisting them and instead rebuilds registry bindings per runtime.

### Constrained declarative semantics

The shipped `observe` and `state` helpers are intentionally thin wrappers over
the canonical snapshot/find/action paths. They support only the current limited
set of surface activation and node action/state transitions rather than a fully
general semantic state engine.

## Follow-on Architecture

Future phases can extend the same snapshot contract with:

- screenshot/mark fallback
- external accessibility adapters
- broader declarative semantics beyond the current constrained `observe/state`
  wrapper layer

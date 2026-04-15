<!-- codex-design -->
# UI Access Protocol — Architecture

**Feature:** `ui_access_protocol`
**Date:** 2026-04-15
**Status:** Implemented v1 architecture

## Goal

Provide one internal semantic UI protocol that all repo-local test, MCP, skill,
and plugin flows can target without re-deriving UI state in different ways.

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
- bridging lifecycle changes into canonical access events
- preserving active-surface semantics

### Test API layer

`src/app/ui.test_api/handler.spl`

Owns additive HTTP contract routes:

- `GET /api/test/ui/snapshot`
- `GET /api/test/ui/surface?id=...`
- `GET /api/test/ui/history?...`
- `POST /api/test/ui/act`

The existing `/api/test/*` contract remains valid.

### MCP OS tool layer

`src/os/services/llm/mcp_os_server.spl`
`src/os/services/llm/tool_registry.spl`

Own:

- LLM-facing tool registration
- window metadata overlay on access surfaces
- canonical action dispatch
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

### Event model

Recent access events are bounded, append-only in memory, and surface-scoped.
They are intended for debugging and short-horizon history, not as a persistent
audit log.

## Hot Paths

### Snapshot read

1. read current session state and surface inventory
2. collect node metadata from in-memory trees/widget registry
3. optionally overlay WM window metadata
4. serialize to JSON or text

### Find

1. build or fetch current snapshot
2. filter nodes in memory by surface/kind/text/focus
3. render filtered text or JSON response

### Action

1. resolve surface and optional canonical node
2. set active surface
3. dispatch an existing `UIEvent.Action`
4. render/refresh

## Cache and Invalidation Strategy

- v1 uses existing in-memory session/surface state as its cache
- access snapshots are rebuilt on demand from that state
- event history is invalidated naturally by bounded append-only replacement
- no extra persistent index is introduced in the hot path

This keeps the first release simple and avoids stale parallel caches.

## Risks

### Legacy action naming

The current system still dispatches through action-name strings such as
`click_widgetId`. The protocol wraps that behavior but does not replace it in
v1.

### Surface/tree mismatch

Window metadata and surface trees are maintained in different subsystems. The
MCP layer therefore overlays window metadata onto surfaces instead of forcing a
deep refactor in v1.

### Event granularity

Recent events are bounded and in-memory only. This is enough for local debug and
LLM workflows, but not for long-lived audit requirements.

## Follow-on Architecture

Future phases can extend the same snapshot contract with:

- screenshot/mark fallback
- external accessibility adapters
- persisted history or indexing
- declarative aliases over raw actions

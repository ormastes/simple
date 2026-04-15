# UI Access Protocol — Requirements

**Date:** 2026-04-15
**Status:** Selected requirements
**Options Source:** `doc/02_requirements/feature/ui_access_protocol_options.md`

## Scope

The feature adds a canonical internal UI access protocol over existing Simple UI
surfaces. It is not an external OS accessibility integration in v1.

## Functional Requirements

### F1: Canonical access model

- REQ-UAP-001: The system shall expose a canonical access snapshot containing
  protocol version, mode, active surface, surfaces, nodes, and recent events.
- REQ-UAP-002: Every canonical node shall expose a stable human-readable ID in
  the form `surface_id#widget_id`.
- REQ-UAP-003: The canonical access model shall be materialized from existing
  `UISession`, `UITree`, widget-registry, and `SurfaceManager` state rather than
  a separate parallel tree.

### F2: Surface-aware access

- REQ-UAP-004: The system shall treat named surfaces as first-class units with
  `surface_id`, title, active-state, and root canonical node identity.
- REQ-UAP-005: The system shall support access snapshots spanning multiple
  surfaces, not only the main tree.
- REQ-UAP-006: The system shall keep existing single-surface behavior working
  for callers that still use the legacy widget/test routes.

### F3: History and actions

- REQ-UAP-007: The session shall record bounded recent access events with
  surface-scoped metadata.
- REQ-UAP-008: The system shall expose recent history for all surfaces and for a
  selected surface.
- REQ-UAP-009: The system shall expose a canonical action path that can target a
  surface directly or a canonical node ID.
- REQ-UAP-018: When an access store is attached, history reads and node-search
  reads shall prefer persisted UI-access data and fall back to in-memory session
  state when no durable data is available.

### F4: HTTP/test API

- REQ-UAP-010: The shared test API shall add additive routes under
  `/api/test/ui/*` for snapshot, surface, history, action, observe, state,
  query, and ensure.
- REQ-UAP-011: The new routes shall preserve the existing shared error-model
  style used by `/api/test/*`.
- REQ-UAP-012: Existing `/api/test/element`, `/api/test/elements`,
  `/api/test/state`, and `/api/test/screenshot` routes shall remain available.

### F5: MCP/LLM tooling

- REQ-UAP-013: The MCP OS tool surface shall register `ui_access_snapshot`,
  `ui_access_surface`, `ui_access_find`, `ui_access_act`,
  `ui_access_history`, `ui_access_observe`, `ui_access_state`,
  `ui_access_query`, and `ui_access_ensure`.
- REQ-UAP-014: The new tool schemas and dispatcher shall stay aligned and have
  automated coverage.
- REQ-UAP-015: Human-readable UI tree text used by screen/debug helpers shall be
  derived from the canonical access snapshot rather than a second ad hoc text
  formatter.
- REQ-UAP-019: Window metadata exposed on canonical surfaces shall be resolved
  through one shared runtime window-to-surface registry rather than per-tool
  overlay logic.

### F6: Plugin and skill packaging

- REQ-UAP-016: The repository shall include a plugin bundle that documents the
  new UI-access workflow for agent/plugin-marketplace use.
- REQ-UAP-017: The repository shall include a Codex `simple-ui` skill that
  teaches snapshot, find, query, observe, state, act, history, and debugging
  flow on top of the shared protocol.

## Acceptance Criteria

- AC-UAP-01: A session with multiple named surfaces returns a canonical snapshot
  with distinct surfaces and canonical node IDs.
- AC-UAP-02: Recent access events can be queried for all surfaces and for one
  selected surface.
- AC-UAP-03: `/api/test/ui/snapshot`, `/api/test/ui/surface`,
  `/api/test/ui/history`, `/api/test/ui/act`, `/api/test/ui/observe`,
  `/api/test/ui/state`, `/api/test/ui/query`, and `/api/test/ui/ensure`
  respond with stable additive behavior.
- AC-UAP-04: The MCP tool registry lists the nine UI access tools with
  matching schemas, and the declarative observe/state/query/ensure tools
  preserve canonical node IDs while routing through the shared protocol.
- AC-UAP-05: Existing widget routes and tests still pass after the feature lands.
- AC-UAP-06: With a UI access store attached, persisted history and persisted
  node search survive restart-level reuse of the same database.
- AC-UAP-07: Window metadata on access surfaces is consistent across test and
  MCP reads because both derive from the shared runtime registry.

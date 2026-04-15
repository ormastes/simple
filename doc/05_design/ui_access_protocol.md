<!-- codex-design -->
# UI Access Protocol — Detail Design

**Feature:** `ui_access_protocol`
**Date:** 2026-04-15
**Status:** Implemented baseline

## Overview

The detail design turns current UI runtime state into one canonical access
protocol that can be consumed by HTTP test routes, MCP tools, and agent docs.

## Module Design

### `src/lib/common/ui/access.spl`

Responsibilities:

- define protocol structs
- convert trees and widget registry records into canonical nodes
- provide recent-event helpers
- provide snapshot find/filter helpers
- serialize protocol objects for API and tool responses

### `src/lib/common/ui/session.spl`

Responsibilities:

- store bounded `access_events`
- increment event sequence numbers
- expose access snapshot/history methods
- attach and route through `UiAccessStore`
- own the shared runtime window-surface registry
- convert lifecycle diffs and dispatched actions into `UiAccessEvent`

### `src/app/ui.test_api/handler.spl`

Responsibilities:

- accept optional `UISession`
- serve additive `/api/test/ui/*` routes, including declarative observe/state
  reads and writes
- fall back to state-derived snapshot when session is absent

### `src/os/services/llm/mcp_os_server.spl`

Responsibilities:

- dispatch the new UI access tools
- provide declarative `ui_access_observe` and `ui_access_state` shims over the
  canonical snapshot/find/action paths
- prefer persisted history and node search when a store is attached
- reuse canonical snapshot text rendering for screen/debug output
- route actions through the existing event-dispatch path

## Data Structure Notes

### `UiAccessNode`

- `canonical_id`: stable readable ID
- `kind`: widget kind from widget registry
- `visible/focused/enabled/selected`: normalized state bits
- `text`: primary text prop
- `props`: non-internal props
- `child_ids`: canonical child references
- `action_names`: derived action list

### `UiAccessSnapshot`

Carries only the current state and bounded history needed for interactive
tooling. Persisted snapshots are derived from it by stripping runtime
`window_id` bindings before storage.

## Error Handling

- invalid or missing `surface_id` -> explicit route/tool errors
- invalid `canonical_id` -> explicit route/tool errors
- invalid `state_key` or unsupported declarative transition -> explicit route
  or tool error
- absent session in HTTP test API -> empty/history-less fallback response
- missing surface on update/action -> error string or `404`-style response
- attached store unavailable or query failure -> fall back to live in-memory
  snapshot/history behavior

## Compatibility Design

- keep legacy widget tools/routes intact
- add new routes and tools rather than mutating old names
- keep declarative observe/state helpers as compatibility wrappers rather than a
  second execution model
- reuse `UIEvent.Action` so action execution semantics remain compatible with
  current render/update flow

## Verification Mapping

- REQ-UAP-001 / 002 / 007 / 008 -> `test/unit/app/ui/access_spec.spl`
- REQ-UAP-010 -> `test/unit/app/ui/ui_access_http_spec.spl`,
  `test/system/ui/ui_access_contract_spec.spl`
- REQ-UAP-013 / 014 -> `test/unit/os/services/llm/tool_registry_spec.spl`,
  `test/unit/os/services/llm/ui_access_dispatch_spec.spl`
- REQ-UAP-018 / NFR-UAP-013 -> `test/unit/app/ui/ui_access_runtime_spec.spl`,
  `test/unit/app/ui/ui_access_store_spec.spl`
- REQ-UAP-019 -> `test/unit/app/ui/window_surface_registry_spec.spl`,
  `test/unit/os/services/llm/ui_access_dispatch_spec.spl`
- build/runtime compatibility -> existing build and UI/system suites

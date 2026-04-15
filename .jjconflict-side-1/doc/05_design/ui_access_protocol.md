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
- extract and update typed values for `input`, `textfield`, and `textarea`
  canonical nodes
- define additive adapter-envelope and vision-sidecar contracts
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
- provide additive `ui_access_value` typed value read/write handling
- provide additive `ui_access_adapter_snapshot` and `ui_access_visual_probe`
  read paths over the same canonical snapshot
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

### Typed value handling

- supported node kinds: `input`, `textfield`, `textarea`
- read shape: canonical node identity plus the current typed value
- write shape: canonical node identity plus the replacement typed value
- unsupported kinds fail explicitly instead of falling back to generic state

### Adapter envelope handling

- source metadata is derived from the current live session/surface
- target metadata keeps operation, surface, window, app, and title hints
- the default adapter path resolves through a null adapter so the additive route
  stays usable without external adapter configuration

### Vision sidecar handling

- semantic marks are projected from canonical nodes, not pixels
- the default provider is intentionally read-only and reports structured issues
  when no image reference is available
- future image-backed capture can replace the provider without changing the
  surface/node identity model

## Error Handling

- invalid or missing `surface_id` -> explicit route/tool errors
- invalid `canonical_id` -> explicit route/tool errors
- non-value-bearing node passed to `ui_access_value` -> explicit route/tool
  error
- invalid typed value payload -> explicit route/tool error
- invalid `state_key` or unsupported declarative transition -> explicit route
  or tool error
- absent session in HTTP test API -> empty/history-less fallback response
- missing surface on update/action -> error string or `404`-style response
- attached store unavailable or query failure -> fall back to live in-memory
  snapshot/history behavior

## Compatibility Design

- keep legacy widget tools/routes intact
- add new routes and tools rather than mutating old names
- keep declarative observe/state/value helpers as compatibility wrappers rather
  than a second execution model
- reuse `UIEvent.Action` so action execution semantics remain compatible with
  current render/update flow

## Verification Mapping

- REQ-UAP-001 / 002 / 007 / 008 -> `test/unit/app/ui/access_spec.spl`
- REQ-UAP-010 -> `test/unit/app/ui/ui_access_http_spec.spl`,
  `test/system/ui/ui_access_contract_spec.spl`
- REQ-UAP-013 / 014 -> `test/unit/os/services/llm/tool_registry_spec.spl`,
  `test/unit/os/services/llm/ui_access_dispatch_spec.spl`
- REQ-UAP-020 / 021 -> `test/unit/app/ui/access_spec.spl`,
  `test/unit/os/services/llm/ui_access_dispatch_spec.spl`,
  `test/unit/app/ui/ui_access_http_spec.spl`,
  `test/system/ui/ui_access_contract_spec.spl`,
  `doc/06_spec/app/os/feature/ui_access_protocol_spec.spl`
- REQ-UAP-022 / 023 -> `test/unit/app/ui/ui_access_adapter_spec.spl`,
  `test/unit/app/ui/ui_access_vision_spec.spl`,
  `test/unit/os/services/llm/ui_access_dispatch_spec.spl`,
  `test/unit/app/ui/ui_access_http_spec.spl`,
  `test/system/ui/ui_access_contract_spec.spl`
- REQ-UAP-018 / NFR-UAP-013 -> `test/unit/app/ui/ui_access_runtime_spec.spl`,
  `test/unit/app/ui/ui_access_store_spec.spl`
- REQ-UAP-019 -> `test/unit/app/ui/window_surface_registry_spec.spl`,
  `test/unit/os/services/llm/ui_access_dispatch_spec.spl`
- build/runtime compatibility -> existing build and UI/system suites

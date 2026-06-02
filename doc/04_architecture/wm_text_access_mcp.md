<!-- codex-design -->
# WM Text Access MCP — Architecture

Status: Implemented first slice.

This architecture is based on the selected Feature Option B and NFR Option 2.
The first implementation slice is `std.common.ui.win_text_access`, re-exported
through `std.common.ui.access`, with MCP status exposed by
`play_wm_text_status`.

## Problem

TRACE32 MCP can inspect and manipulate MDI/text windows because TRACE32 exposes semantic window commands, AREA text buffers, `WinPrint.*`, and action catalogs. Existing host WM tooling can enumerate/focus/type/click top-level windows, but it cannot see arbitrary controls inside a foreign app. Existing Simple UI access can expose semantic nodes, but only for in-process Simple surfaces.

The architecture must let CLI, service, and MCP clients use the same snapshot/query/action logic across these sources without pretending that all backends have the same semantic depth.

## Existing Anchors

- `src/lib/common/ui/access*.spl`: canonical UI access snapshot/query/source helpers.
- `src/lib/common/ui/window_surface_registry.spl`: runtime mapping between top-level windows and UI surfaces.
- `src/lib/nogc_sync_mut/play/wm/mod.spl`: host WM shell adapter for screenshot, window list, focus, click, type, key.
- `src/app/mcp/main_lazy_play_tools.spl`: existing MCP handlers for `play_wm_*` and `play_ui_*`.
- `examples/10_tooling/trace32_tools/t32_mcp/window_tools.spl`: TRACE32 catalog, window list/open/capture/describe handlers.
- `examples/10_tooling/trace32_tools/t32_mcp/snapshot_store.spl`: TRACE32 capture/diff storage precedent.

## Pattern

Use an adapter envelope over existing semantic sources.

```text
CLI / service / MCP
        |
wm_text_access facade
        |
shared access core: snapshot, query, find, act, value, history
        |
adapter envelope with source/capability/staleness metadata
        |
+-------------------+-------------------+-------------------+
| TRACE32 adapter   | Simple UI adapter | Host WM adapter   |
| catalog/AREA/text | common.ui.access  | std.play.wm       |
+-------------------+-------------------+-------------------+
```

## Layer Responsibilities

### Facade Layer

The facade exposes stable operations:

- snapshot
- surface
- find/query
- act
- value
- history
- adapter status

It is the only layer used by CLI/service/MCP entrypoints.

### Shared Access Core

The shared core owns backend-independent behavior:

- canonical surface and node IDs
- selector matching
- text/role/kind/state filtering
- action routing by capability
- value read/write capability checks
- unsupported-operation errors
- recent history/event recording
- response envelopes with source, confidence, capabilities, captured time, max age, and staleness

### Adapter Layer

Adapters only materialize snapshots and execute backend-specific operations. They do not own query semantics.

Required first-step adapters:

- TRACE32 window adapter:
  - source: catalog entries, actions, fields, `WinPrint.*`, `PRinTer.FILE`, AREA output
  - semantic depth: window and text-field level when captures are parseable
- Simple UI adapter:
  - source: existing `common.ui.access` snapshots
  - semantic depth: surface/node/action/value where already supported
- Host WM adapter:
  - source: `std.play.wm` window list/focus/input/screenshot
  - semantic depth: top-level windows only
  - internal controls: unsupported unless a future accessibility adapter supplies them

Future adapters:

- Windows UIA
- macOS AX
- Linux AT-SPI
- screenshot/vision sidecar

## MDSOC Boundary

This feature is a virtual capsule around "external UI access". It crosses app, common UI, play/WM, and TRACE32 tooling. The capsule boundary is:

- public facade: `wm_text_access`
- shared model/query/action core: `common.ui.access` compatible structures
- private adapters: backend-specific conversion and execution

Platform-specific subprocess calls, remote API calls, and accessibility APIs must remain below the adapter boundary.

## Startup Path

- MCP startup must not refresh TRACE32 windows, enumerate OS windows, or run accessibility scans.
- CLI/service startup may load static schemas and adapter registrations only.
- Adapter refresh occurs on explicit snapshot/query requests or explicit refresh flags.

## Hot Request Path

- In-memory query/filter/action checks run against a current snapshot.
- Remote/shell-backed adapters must not perform repeated full refreshes for every query.
- Refresh policy is per adapter:
  - Simple UI: live in-process snapshot, no shell-out.
  - TRACE32: command/capture refresh only when requested or stale.
  - Host WM: window list refresh cached with max age; focus/type/click execute direct operations.

## Cache And Invalidation

- Every snapshot carries `captured_at`, `max_age_ms`, and `stale`.
- Explicit refresh invalidates adapter cache.
- Mutating actions invalidate the affected adapter/surface cache.
- Unsupported or unavailable adapters report status instead of falling back silently.

## Performance Targets

These targets follow the recommended NFR Option 2:

- In-memory snapshot/query/action p95 under 20 ms on representative fixtures.
- Shell/remote adapters expose staleness and avoid repeated shell-outs on hot query paths.
- Adapter refresh timings are observable through debug/status output.

## Risks

- Host WM data is not semantic control data.
- Wayland may limit window control.
- TRACE32 captures may be stale until `SCREEN.WAIT` or an explicit refresh completes.
- Accessibility adapters require permissions and must be added behind the same capability model.

## Implementation Placement

- shared core: `src/lib/common/ui/win_text_access.spl`
- hub export: `src/lib/common/ui/access.spl`
- MCP status integration: `src/app/mcp/main_lazy_play_tools.spl`,
  `src/app/mcp/main_dispatch.spl`, and `src/app/mcp/tool_table.spl`
- live MCP scalar facade: `play_wm_text_snapshot`, `play_wm_text_find`, and
  `play_wm_text_act`
- CLI planner discovery: `simple play wm-text-snapshot`,
  `simple play wm-text-find`, and `simple play wm-text-act`
- system spec: `test/system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl`
- generated/manual spec: `doc/06_spec/system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.md`

The first slice supplies reusable TRACE32 captured-text, Simple UI snapshot, and
host WM top-level adapters. Live TRACE32 refresh/open/capture execution remains
owned by the existing TRACE32 MCP/window tooling; the common layer owns the
normalized text/query/action contract.

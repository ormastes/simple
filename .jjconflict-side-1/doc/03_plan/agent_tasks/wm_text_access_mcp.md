<!-- codex-research -->
# WM Text Access MCP — Agent Task Plan

Date: 2026-06-01

## Status

Planning based on research recommendation. Implementation is gated on selected requirements:

- Feature options: `doc/02_requirements/feature/wm_text_access_mcp_options.md`
- NFR options: `doc/02_requirements/nfr/wm_text_access_mcp_options.md`

Recommended path from research:

- Feature Option B: Shared Adapter Envelope Around Existing Sources
- NFR Option 2: Adapter Contract Production Gate

## Goal

Build a shared WM text-access layer that normalizes TRACE32 text/MDI windows, Simple UI access snapshots, and host WM top-level windows into one snapshot/query/action model for CLI, service, and MCP clients.

## Implementation Sequence

### 1. Requirement Selection

- Confirm selected feature and NFR options.
- Write:
  - `doc/02_requirements/feature/wm_text_access_mcp.md`
  - `doc/02_requirements/nfr/wm_text_access_mcp.md`
- Delete unchosen option files after final requirements are written.

### 2. Design

- Write architecture doc:
  - `doc/04_architecture/wm_text_access_mcp.md`
- Write detail design:
  - `doc/05_design/wm_text_access_mcp.md`
- Cover:
  - adapter interface
  - snapshot model
  - node/surface IDs
  - query/find rules
  - action routing
  - value operation capability checks
  - source/confidence/capability/staleness metadata
  - cache and invalidation strategy
  - CLI/service/MCP entrypoints

### 3. System Tests

- Write executable SPipe spec:
  - `test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl`
- Generate/read manual spec doc:
  - `doc/06_spec/system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.md`
- Test scenarios:
  - TRACE32 catalog window appears as a text-access surface.
  - TRACE32 captured text can be queried by field/text.
  - Simple UI canonical snapshot can be wrapped by the adapter envelope.
  - Host WM top-level window list exposes window surfaces with limited capabilities.
  - Unsupported value/action operations return structured unsupported errors.
  - Query/action helpers use shared core behavior across adapters.
  - Hot-path query avoids repeated shell-outs for cached adapter data.

### 4. Core Implementation

- Add shared access core under an owned library path.
- Implement common structs/classes for:
  - adapter status
  - surface snapshot
  - access node
  - query selector
  - action request/result
  - value request/result
  - source/capability/staleness metadata
- Add shared query/find/action helpers.

### 5. First Adapters

- TRACE32 adapter:
  - normalize catalog entries, `WinPrint`/`PRinTer.FILE` captures, AREA output, actions, and fields.
- Simple UI adapter:
  - wrap existing canonical UI access snapshots without changing their base contract.
- Host WM adapter:
  - wrap `std.play.wm` top-level window enumeration, focus, type, click, screenshot where available.
  - mark internal controls unsupported unless a semantic adapter supplies them.

### 6. Entrypoints

- Add or extend CLI/service/MCP tool surfaces:
  - snapshot
  - surface
  - find/query
  - act
  - value
  - history/status
- Ensure all entrypoints call shared core helpers rather than duplicating adapter-specific query/action behavior.

### 7. Verification

- Run SPipe specs.
- Run focused unit/integration tests for touched modules.
- Run MCP/core smoke checks if shared `src/lib/**` or MCP surfaces change.
- Verify no executable specs were placed under `doc/06_spec`:
  - `find doc/06_spec -name '*_spec.spl' | wc -l`

## Open Gate

Implementation must wait for explicit requirement selection unless the user confirms the recommended Feature Option B and NFR Option 2.


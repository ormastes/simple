<!-- codex-research -->
# WM Text Access MCP — Feature Requirements

Status: Selected requirements

Selected path: common window-to-text module with shared adapter envelope. Based on Feature Option B, extended by user request to make TRACE32, Simple UI, and WM sources use the common module.

## Scope

Build a common window-to-text access module that normalizes TRACE32 text/MDI windows, Simple UI access surfaces, and host WM top-level windows into one snapshot/query/action model for CLI, service, and MCP use.

## Functional Requirements

REQ-WTA-001: Common model

The system shall expose shared window-to-text data types for source metadata, capabilities, surfaces, nodes, snapshots, selectors, action requests, and action results.

REQ-WTA-002: Shared query logic

The system shall implement selector/query logic once in the common module and use it for TRACE32, Simple UI, and host WM snapshots.

REQ-WTA-003: Shared action routing

The system shall implement common action validation and routing helpers that reject unsupported operations with structured errors before backend-specific execution.

REQ-WTA-004: TRACE32 adapter shape

The system shall expose TRACE32 text/MDI windows as window-to-text surfaces with catalog/open/capture/action metadata and text nodes suitable for shared query.

REQ-WTA-005: Simple UI adapter shape

The system shall expose Simple UI canonical access surfaces through the same window-to-text envelope without replacing the existing Simple UI access protocol.

REQ-WTA-006: Host WM adapter shape

The system shall expose host WM top-level windows through the same window-to-text envelope and mark internal control access unsupported unless a semantic adapter supplies it.

REQ-WTA-007: CLI/service/MCP readiness

The system shall provide shared APIs that CLI, service, and MCP handlers can call without duplicating backend-specific query/action logic.

REQ-WTA-008: Extensibility

The system shall allow future UIA, AX, AT-SPI, and visual sidecar adapters to join the same source/capability/staleness model.

## Acceptance Criteria

- AC-WTA-01: A TRACE32-style window catalog entry and captured text produce a queryable window-to-text snapshot.
- AC-WTA-02: A Simple UI-style surface/node set can be wrapped as a window-to-text snapshot while preserving IDs.
- AC-WTA-03: A host WM window list can be wrapped as window-to-text surfaces with top-level capabilities only.
- AC-WTA-04: Shared selector queries return matching nodes across TRACE32, Simple UI, and host WM fixture snapshots.
- AC-WTA-05: Unsupported host WM child-control or value operations return structured unsupported-operation results.
- AC-WTA-06: Shared action helpers route supported actions and reject unsupported actions without backend-specific query duplication.

## Out Of Scope

- Full Windows UIA, macOS AX, and Linux AT-SPI adapters.
- Screenshot/OCR-only manipulation of arbitrary controls.


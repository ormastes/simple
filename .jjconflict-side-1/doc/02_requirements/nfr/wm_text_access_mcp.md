<!-- codex-research -->
# WM Text Access MCP — NFR Requirements

Status: Selected NFRs

Selected path: NFR Option 2, adapter contract production gate.

## NFRs

NFR-WTA-001: Capability transparency

Every snapshot, surface, and action result shall expose source and capability metadata so callers can distinguish semantic TRACE32/Simple UI data from host WM top-level data.

NFR-WTA-002: Staleness transparency

Adapter-backed snapshots shall expose captured time, max age, and stale status.

NFR-WTA-003: Hot-path behavior

Shared selector/query logic shall operate on in-memory snapshots and shall not shell out or refresh remote adapters.

NFR-WTA-004: Unsupported operation safety

Unsupported operations shall return structured unsupported results instead of silently falling back to lower-confidence behavior.

NFR-WTA-005: Extensibility

The shared model shall be adapter-neutral and leave room for UIA, AX, AT-SPI, and visual sidecar adapters without changing the public query/action core.

NFR-WTA-006: Verification

Tests shall cover TRACE32-style, Simple UI-style, host WM-style, query, action, and unsupported-operation behavior with real assertions and no placeholder passes.

NFR-WTA-007: Layout safety

Executable SPipe specs shall not be placed under `doc/06_spec`.


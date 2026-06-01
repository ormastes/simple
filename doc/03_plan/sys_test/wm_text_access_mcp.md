<!-- codex-research -->
# WM Text Access MCP — System Test Plan

Date: 2026-06-01

## Scope

System tests should verify the shared text-access behavior across adapter classes without requiring a live platform accessibility stack in the first implementation.

## Planned Executable Spec

`test/system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl`

## Scenario Coverage

### Scenario 1: TRACE32 Text Window Surface

Given a TRACE32-style catalog entry with title, open command, capture command, capture mode, fields, and actions.
When the TRACE32 adapter builds a snapshot.
Then the snapshot exposes a surface with TRACE32 source metadata, stable IDs, capture capability, and action capability.

### Scenario 2: TRACE32 Text Query

Given captured TRACE32 window text with register-like fields.
When a query searches by text or field name.
Then the shared query helper returns matching nodes without backend-specific parsing in the MCP layer.

### Scenario 3: Simple UI Adapter Envelope

Given an existing canonical Simple UI access snapshot.
When the Simple UI adapter wraps it.
Then node IDs, surface IDs, and value-bearing controls remain intact and source metadata identifies the Simple UI adapter.

### Scenario 4: Host WM Top-Level Windows

Given host WM window metadata equivalent to `std.play.wm` output.
When the host WM adapter builds a snapshot.
Then top-level windows appear as surfaces and unsupported internal control operations are reported as unsupported.

### Scenario 5: Shared Action Routing

Given adapters with different capabilities.
When action requests target a TRACE32 action, a Simple UI node action, and a host WM focus action.
Then the shared action router dispatches only supported operations and returns structured errors for unsupported operations.

### Scenario 6: Capability And Staleness Metadata

Given cached adapter data.
When a snapshot or query result is returned.
Then the response includes source, capabilities, confidence, captured time or max age, and staleness status.

### Scenario 7: Hot Path Guard

Given repeated queries against cached adapter data.
When the same query runs multiple times.
Then query execution uses the shared in-memory snapshot/query path and does not invoke adapter refresh on every call.

## Verification Rules

- Use built-in SPipe matchers only.
- Do not use placeholder assertions such as `expect(true).to_equal(true)`.
- Generated manual documentation belongs under `doc/06_spec/.../*.md`.
- No executable `.spl` files may be placed under `doc/06_spec`.


# Feature Specification - MCP Protocol Compliance and Gap Tracking

**Plan:** [doc/plan/mcp_protocol_gap_closure_plan_2026-02-24.md](../../plan/mcp_protocol_gap_closure_plan_2026-02-24.md)  
**Design:** [doc/design/simple_mcp_debug_design.md](../../design/simple_mcp_debug_design.md)  
**Research:** [doc/research/mcp_command_and_response_gap_analysis_2026-02-24.md](../../research/mcp_command_and_response_gap_analysis_2026-02-24.md)  
**Status:** In Progress

## Feature Description

Ensure active `simple-mcp` provides a protocol surface and response format compatible with practical MCP clients (including Python and Rust SDK ecosystems), while preserving current debug tool usability.

## Scenarios

### Scenario: Core MCP Lifecycle Works

**Given** a client connects over stdio  
**When** it sends `initialize`, `initialized`, and `shutdown`  
**Then** the server returns valid JSON-RPC responses and exits cleanly

### Scenario: Debug Tooling Available Across Clients

**Given** the client calls `tools/list`  
**When** it searches for debug and debug-log tools  
**Then** all expected debug tool names are present and callable

### Scenario: Protocol Gap Visibility

**Given** known missing methods are not implemented yet  
**When** protocol coverage is reviewed  
**Then** each missing method is explicitly tracked in docs and SSpec matrix tests

### Scenario: Response Format Gap Visibility

**Given** known response-shape mismatches exist  
**When** format compatibility is reviewed  
**Then** each mismatch is explicitly tracked in docs and SSpec matrix tests

## Acceptance Criteria

- [ ] Feature inventory (all current MCP tools) is documented and mirrored in SSpec matrix.
- [ ] Gap inventory (methods + response format) is documented and mirrored in SSpec matrix.
- [ ] Closure plan phases are documented and mirrored in SSpec matrix.
- [ ] Design document includes current implementation path and explicit protocol deltas.

## Out of Scope

- Full immediate closure of all protocol gaps in this documentation pass.
- Runtime/backend-level debugger parity with full `main.spl` execution path.

## Test Coverage

| Scenario | Spec file | Status |
|----------|-----------|--------|
| Core lifecycle inventory | `test/feature/app/mcp_protocol_gap_matrix_spec.spl` | Added |
| Debug and diagnostic feature inventory | `test/feature/app/mcp_protocol_gap_matrix_spec.spl` | Added |
| Gap inventory lock | `test/feature/app/mcp_protocol_gap_matrix_spec.spl` | Added |
| Runtime protocol method coverage | `test/feature/app/mcp_protocol_runtime_spec.spl` | Added |
| Existing debug-log behavior | `test/feature/app/mcp_debug_log_spec.spl` | Existing |

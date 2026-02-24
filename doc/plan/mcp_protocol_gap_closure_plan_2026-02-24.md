# MCP Protocol Gap Closure Plan (2026-02-24)

## Objective

Close protocol and response-format gaps between active `simple-mcp` (`main_lazy`) and MCP servers commonly built with Python/Rust SDKs, while preserving the current fast startup path.

## Current Baseline

- Active server path: `bin/simple_mcp_server -> src/app/mcp/main_lazy.spl`
- Debug tools: implemented and cross-client verified (Python, TypeScript, Rust probes)
- Protocol surface: partial

Reference analysis:
- `doc/research/mcp_command_and_response_gap_analysis_2026-02-24.md`

## Feature Inventory (Current)

### Tooling Features

- Debug tools (16): `debug_create_session`, `debug_list_sessions`, `debug_close_session`, `debug_set_breakpoint`, `debug_remove_breakpoint`, `debug_continue`, `debug_step`, `debug_get_variables`, `debug_stack_trace`, `debug_evaluate`, `debug_set_function_breakpoint`, `debug_enable_breakpoint`, `debug_get_source`, `debug_watch`, `debug_set_variable`, `debug_terminate`
- Debug log tools (6): `debug_log_enable`, `debug_log_disable`, `debug_log_clear`, `debug_log_query`, `debug_log_tree`, `debug_log_status`
- Diagnostic tools (12): `simple_read`, `simple_check`, `simple_symbols`, `simple_status`, `simple_edit`, `simple_multi_edit`, `simple_run`, `simple_diff`, `simple_log`, `simple_squash`, `simple_new`, `simple_api`

### Protocol Features

- Implemented: `initialize`, `initialized`, `shutdown`, `ping`, `tools/list`, `tools/call`, `resources/list`, `prompts/list`
- Missing: `resources/templates/list`, `resources/read`, `prompts/get`, `completion/complete`, `completions/complete`, `logging/setLevel`, roots API

## Gap Inventory

### Gap Group A: Missing MCP Methods

1. `resources/templates/list`
2. `resources/read`
3. `prompts/get`
4. `completion/complete` and alias handling for `completions/complete`
5. `logging/setLevel`
6. `roots/list` and roots-related notifications

### Gap Group B: Response Format Inconsistencies

1. JSON-RPC `id` type not preserved (`"1"` request can return `1`)
2. Under-declared capabilities in `initialize` response
3. Generic tool schemas only (`{"type":"object"}` with no field-level details)
4. Tool/domain errors returned as JSON-RPC errors instead of tool-level `isError` style
5. Debug tool payloads encoded as JSON-in-text only (no structured payload)

## Implementation Plan

### Phase 1: Protocol Correctness (P0)

Status: Implemented in current pass.

1. Added raw id extraction and response id echo preservation in `main_lazy`.
2. Verified string id remains string in response.
3. Added runtime SSpec coverage for id preservation.

### Phase 2: Method Completeness (P1)

Status: Implemented in current pass.

1. Implemented `resources/templates/list`.
2. Implemented `resources/read` for:
   - `project:///info`
   - `file:///...`
   - `debuglog:///status`
3. Implemented `prompts/get`.
4. Implemented `completion/complete` and `completions/complete` alias.
5. Implemented `logging/setLevel` and `roots/list`.

### Phase 3: Capability and Schema Quality (P2)

Status: Implemented in current pass.

1. Expanded `initialize.capabilities` to include resources/prompts/logging/completions/roots.
2. Upgraded tool schemas with `properties` and `required`.
3. Annotation parity is partially represented; full hint tuning remains optional refinement.

### Phase 4: Error and Payload Semantics (P3)

Status: Implemented in current pass.

1. Kept JSON-RPC errors for protocol-level failures.
2. Return tool-level failures via result payload with `isError=true`.
3. Added `structuredContent` alongside text payload for tool results.

## SSpec Coverage Plan

Primary spec file:
- `test/feature/app/mcp_protocol_gap_matrix_spec.spl`

Runtime wire spec:
- `test/feature/app/mcp_protocol_runtime_spec.spl`

Coverage goals:
1. Full feature inventory lock (tool counts and names).
2. Full gap inventory lock (missing methods + format gaps).
3. Plan-phase lock (ensures all planned phases remain documented in tests).

Follow-up execution spec (next step):
1. Add active round-trip protocol tests once Phase 1 and 2 methods are implemented.
2. Validate wire responses for both Content-Length and JSON-lines framing.

## Deliverables

1. Plan: this file
2. Design update: `doc/design/simple_mcp_debug_design.md` (current state + deltas)
3. Feature doc: `doc/feature/app/mcp_protocol_compliance.md`
4. Spec doc: `doc/spec/feature/app/mcp_protocol_compliance_spec.md`
5. SSpec matrix: `test/feature/app/mcp_protocol_gap_matrix_spec.spl`

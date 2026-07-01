# MCP Command and Response Gap Analysis (2026-02-24)

## Scope

This document compares the active `simple-mcp` server behavior (currently `bin/simple_mcp_server -> src/app/mcp/main_lazy.spl`) against:

1. MCP protocol expectations (2025-06-18 schema and docs)
2. Typical behavior produced by Python MCP SDK servers
3. Typical behavior produced by Rust `rmcp` SDK servers

Focus: **missing commands** and **response format mismatches**.

## Baseline Tested

- Configured server: `.mcp.json` -> `bin/simple_mcp_server`
- Active implementation path: `src/app/mcp/main_lazy.spl`
- Verification clients executed:
  - `scripts/mcp_probes/probe_debug_python.py`
  - `scripts/mcp_probes/probe_debug_typescript.ts`
  - `scripts/mcp_probes/probe_debug_rust.rs`

## Status Update (After Full Implementation Pass)

Resolved in `main_lazy`:

- `resources/templates/list`
- `resources/read`
- `prompts/get`
- `completion/complete` (`completions/complete` alias)
- `logging/setLevel`
- `roots/list`
- JSON-RPC id type preservation (string id remains string in response)

Resolved in this pass:

- Capability declaration expanded (tools/resources/prompts/logging/completions/roots)
- Detailed tool input schemas with `properties` and `required`
- Tool-level `isError` result semantics for tool/domain failures
- Structured content added to tool results (`structuredContent`)

## Observed Command Support (main_lazy)

### Supported

- `initialize`
- `initialized` / `notifications/initialized`
- `shutdown`
- `ping`
- `tools/list`
- `tools/call`
- `resources/list` (returns empty list)
- `prompts/list` (returns empty list)
- `notifications/cancelled`

### Missing (observed as `-32601 Method not found`)

- `resources/templates/list`
- `resources/read`
- `prompts/get`
- `completion/complete`
- `completions/complete`
- `logging/setLevel` (not implemented)
- `roots/list` and roots-change notifications (not implemented)

### Evidence Sample

Request/response probe against `bin/simple_mcp_server`:

- `resources/templates/list` -> `{"error":{"code":-32601,"message":"Method not found: resources/templates/list"}}`
- `resources/read` -> `{"error":{"code":-32601,"message":"Method not found: resources/read"}}`
- `prompts/get` -> `{"error":{"code":-32601,"message":"Method not found: prompts/get"}}`
- `completion/complete` -> `{"error":{"code":-32601,"message":"Method not found: completion/complete"}}`

## Response Format Gaps

### 1. JSON-RPC `id` type is not preserved

Observed behavior:

- Request uses string id: `"id":"1"`
- Response returns numeric id: `"id":1`

Why this matters:

- JSON-RPC permits string/number ids, but response should echo the same id value/type used by the request.
- Python/Rust SDK-based servers preserve id via proper JSON parsing/serialization.

Likely root cause:

- `main_lazy` extracts fields using string slicing instead of typed JSON parsing.

### 2. Capabilities are under-declared

Current `initialize` response from `main_lazy`:

- Declares only `tools.listChanged`

Missing capability declarations for features clients expect when available:

- `resources`
- `prompts`
- `completions`
- `logging`

Impact:

- Python/Rust MCP clients often gate behavior based on capabilities.
- Even if a method exists later, clients may never call it if capability is omitted.

### 3. Tool result payload uses JSON embedded as text

Observed for debug tools:

- `result.content[0].text` contains a JSON string (escaped object), not structured fields.

This is valid for plain text tools, but compared with Python/Rust SDK patterns:

- SDK servers commonly return `structuredContent` and/or typed content blocks.
- Error states are often represented via `isError` in `CallToolResult` rather than only JSON-RPC errors.

### 4. Tool execution errors use JSON-RPC `error` for tool-level domain failures

Observed:

- Unknown tool -> JSON-RPC `error` `-32601`

Interop expectation:

- SDK servers commonly return transport-level success for `tools/call` and encode tool failure in `result` with `isError=true` and error text payload.

## Schema Quality Gaps vs SDK-style MCP Servers

`tools/list` currently advertises all tool schemas as:

- `{"type":"object"}`

Missing in many tools:

- `properties`
- `required`
- per-field descriptions
- annotations (`readOnlyHint`, `destructiveHint`, etc.)

Impact:

- Weak auto-completion and parameter validation in clients.
- More malformed calls from LLM agents.

## Cross-SDK Interop Status (What Works Today)

Confirmed by probes:

- Python client: debug flow works (`debug_create_session`, `debug_list_sessions`, `debug_log_enable`, `debug_log_status`)
- TypeScript client: same flow works
- Rust client: same flow works

So **core debug tool round-trip works across SDK ecosystems**, but **protocol surface and response quality are behind SDK-native MCP servers**.

## Gap Matrix (Simple main_lazy vs Python/Rust SDK Typical)

| Area | `main_lazy` now | Python/Rust SDK typical | Gap |
|---|---|---|---|
| Init capabilities | Minimal (tools only) | Full declared capabilities | High |
| Resource API | list only (empty) | list + templates + read | High |
| Prompts API | list only (empty) | list + get | High |
| Completion API | missing | completion endpoint implemented | High |
| JSON-RPC id echo | type not preserved | exact id preserved | Medium |
| Tool schemas | generic object only | detailed JSON schema | Medium |
| Tool error format | JSON-RPC errors for tool failures | `CallToolResult.isError` pattern | Medium |
| Debug tool calls | available and stateful | available depending on server | Good |

## Recommended Fix Order

### Priority 0 (Interop correctness)

1. Preserve JSON-RPC `id` exactly as received (string stays string).
2. Replace string-slice JSON parsing in `main_lazy` with robust JSON helpers.

### Priority 1 (Protocol completeness)

1. Add `resources/templates/list`
2. Add `resources/read`
3. Add `prompts/get`
4. Add `completion/complete`
5. Add capability declarations that match implemented methods

### Priority 2 (Agent quality)

1. Upgrade `tools/list` schemas with `properties` + `required`
2. Add tool annotations (`readOnlyHint`, `destructiveHint`, `idempotentHint`)
3. Return structured tool outputs where possible (`structuredContent`)

### Priority 3 (Error semantics)

1. Use tool-result-level error signaling (`isError=true`) for domain/tool failures
2. Keep JSON-RPC errors for protocol/transport errors only

## Suggested Acceptance Checks

1. JSON-RPC compliance check: send string id and verify string id echoed unchanged.
2. Capability-method consistency check: every declared capability has corresponding implemented method.
3. Method coverage check: verify all core MCP methods return non-`-32601` responses.
4. Schema richness check: each tool with required args must advertise `required` keys.
5. Cross-client probes (Python/TS/Rust) in CI for:
   - init + list + call + shutdown
   - missing-parameter error behavior

## References

- MCP specification docs: https://modelcontextprotocol.io/specification
- MCP 2025-06-18 JSON schema: https://raw.githubusercontent.com/modelcontextprotocol/specification/main/schema/2025-06-18/schema.json
- Python MCP SDK docs: https://modelcontextprotocol.github.io/python-sdk/
- Rust MCP SDK (`rmcp`) docs: https://docs.rs/rmcp

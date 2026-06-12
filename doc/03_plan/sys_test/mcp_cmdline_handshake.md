# MCP Command-Line Handshake Test Plan

## Scope

Validate local Simple-created MCP command wrappers by launching each wrapper as
a command-line process, sending an MCP initialize/initialized/tools-list
handshake, and requiring a bounded response.

Covered wrappers:
- `bin/simple_mcp_server`
- `bin/simple_lsp_mcp_server`
- `bin/t32_mcp_server`
- `bin/t32_lsp_mcp_server`
- `bin/obsidian_lsp_mcp_server`

## Helper Contract

The system spec helper builds JSONL MCP messages, writes them to a temporary
stdin file, launches the wrapper with hosted fallback disabled, and verifies:
- `--json` readiness contains the expected server marker.
- Command exits with status `0`.
- Elapsed time is under `15000 ms`.
- Output contains JSON-RPC initialize and tools/list responses.
- Output contains a representative expected tool marker.
- Output does not report parse errors or native-missing failures.

The helper is pure Simple spec code using stdlib process, file, env, and time
helpers. It must not declare direct `rt_*` externs and must not require Node.js.

## Pass Criteria

All wrappers answer the handshake within the time limit and list tools.

## Current Risk

Native artifact health is part of the contract. If a wrapper refuses its native
artifact or the child process segfaults, the system spec should fail; that is a
server/package bug, not a test-helper pass.

## Execution

```bash
bin/simple check test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl
bin/simple test test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl --native
```

## Traceability

| REQ | Description | Test File | Generated Spec | Coverage |
|-----|-------------|-----------|----------------|----------|
| REQ-MCP-CMD-001 | Local MCP wrappers answer command-line initialize and tools/list handshakes within a time limit | `test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl` | `doc/06_spec/test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md` | Full when all wrappers pass |

# MCP Command-Line Handshake

System test manual for
`test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl`.

## Scenario: REQ-MCP-CMD-001

Local MCP wrappers must launch by command line, report readiness through
`--json`, complete an MCP initialize/initialized/tools-list handshake, and
return a tools list within `15000 ms`.

## Helper

`mcp_cmdline_probe`:
- Creates JSONL MCP handshake input.
- Runs `<wrapper> --json` for readiness metadata.
- Runs the wrapper with stdin redirected from the handshake file.
- Disables source/hosted fallback via environment variables.
- Records exit code, elapsed time, stdout, stderr, readiness JSON, and failure
  reason.

The helper uses Simple stdlib process/file/time/env modules. It does not use
direct `rt_*` extern declarations and does not depend on Node.js.

## Covered Commands

| Command | Readiness marker | Tool marker |
|---------|------------------|-------------|
| `bin/simple_mcp_server` | `Simple MCP Server` | `play_wm_text_status` |
| `bin/simple_lsp_mcp_server` | `simple-lsp-mcp` | `definition` |
| `bin/t32_mcp_server` | `TRACE32 MCP Server` | `t32_` |
| `bin/t32_lsp_mcp_server` | `TRACE32 LSP MCP Server` | `definition` |
| `bin/obsidian_lsp_mcp_server` | `Obsidian LSP MCP Server` | `obsidian` |

## Expected Assertions

- Probe `ok` is `true`.
- Exit code is `0`.
- Elapsed time is less than `15001 ms`.
- Readiness JSON contains the expected server marker.
- Stdout contains the expected tool marker.

## Evidence Commands

```bash
bin/simple check test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl
bin/simple test test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl --native
```

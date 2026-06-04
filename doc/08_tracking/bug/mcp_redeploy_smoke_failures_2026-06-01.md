# MCP redeploy smoke failures - 2026-06-01

## Summary

After syncing `main` to GitHub and rebuilding/deploying the macOS ARM64
`simple` driver, MCP redeploy validation found current MCP failures:

- `bin/simple_mcp_server` starts, but `tools/list` output is not valid JSON for
  the full tool list. The first invalid entries omit the closing object before
  the next tool and expose required schema keys without matching
  `inputSchema.properties`.
- `scripts/check/check-mcp-native-smoke.shs` fails with
  `mcp_tools_json_valid=false`, `mcp_tools_schema_valid=false`, and
  `mcp_tools_count=0`.
- Rebuilding `src/app/mcp/main.spl` on macOS ARM64 with the core-C lane fails at
  link time with duplicate symbols:
  `Architecture.to_string`, `DebugExecutionMode.to_string`, and
  `DebugTransportKind.to_string`.
- Retrying with the fuller compiler/app/lib source set fails while assembling
  generated stubs because macOS clang rejects emitted `.weak` directives.
- `bin/t32_mcp_server` exits with
  `error: failed to compile cached t32_mcp frontend`.
- `bin/t32_lsp_mcp_server` exits non-zero during the same initialize/tools-list
  smoke probe.

## Still working

- `bin/simple` was rebuilt with `cargo build --release -p simple-driver` and
  deployed to `bin/release/aarch64-apple-darwin-macho/simple`.
- `bin/simple --version` reports `Simple Language v1.0.0-beta`.
- `bin/simple_lsp_mcp_server` responds to line-delimited
  initialize/tools-list requests with 11 tools and valid schemas.

## Repro commands

```bash
scripts/check/check-mcp-native-smoke.shs

SIMPLE_LIB=src bin/simple native-build \
  --runtime-bundle core-c \
  --source src/app \
  --entry-closure \
  --entry src/app/mcp/main.spl \
  --strip \
  --output bin/release/aarch64-apple-darwin-macho/simple_mcp_server

printf '%s\n%s\n' \
  '{"jsonrpc":"2.0","id":"1","method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"smoke","version":"1"}}}' \
  '{"jsonrpc":"2.0","id":"2","method":"tools/list","params":{}}' \
  | bin/t32_mcp_server
```

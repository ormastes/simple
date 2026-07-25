# MCP redeploy smoke failures - 2026-06-01

Status: open (triaged 2026-06-11)

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

## 2026-06-06 Codex Follow-Up

Fresh Linux native builds for the MCP package targets initially completed, but
the resulting binaries were not usable MCP servers. They exited silently for
direct `--json` readiness probes and segfaulted under the native smoke protocol
probes:

```bash
bin/simple native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/mcp/main.spl --strip \
  --output build/bootstrap/mcp-package/simple_mcp_server

bin/simple native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip \
  --output build/bootstrap/mcp-package/simple_lsp_mcp_server

build/bootstrap/mcp-package/simple_mcp_server --json

SIMPLE_BINARY=bin/simple \
MCP_SERVER=build/bootstrap/mcp-package/simple_mcp_server \
LSP_MCP_SERVER=build/bootstrap/mcp-package/simple_lsp_mcp_server \
sh scripts/check/check-mcp-native-smoke.shs
```

The smoke script was updated to include structured failure fields:

```text
mcp_server_exit_code=139
lsp_mcp_server_exit_code=139
mcp_tools_json_valid=false
lsp_tools_json_valid=false
```

Follow-up fixes removed native-unsafe entrypoint startup logging, made MCP
method/id detection explicit for native startup, built initialize capabilities
without the fragile JSON splice, and compacted static tool schemas. After those
changes, the package smoke passes:

```bash
SIMPLE_BINARY=bin/simple \
MCP_SERVER=build/bootstrap/mcp-package/simple_mcp_server \
LSP_MCP_SERVER=build/bootstrap/mcp-package/simple_lsp_mcp_server \
sh scripts/check/check-mcp-native-smoke.shs
```

Observed result: MCP JSON/schema valid, 151 MCP tools, WM text tools present,
LSP JSON/schema valid, and 11 LSP tools.

The full MCP build still reports 33 generated unresolved-symbol stubs; the LSP
MCP build reports 485 generated unresolved stubs plus internal symbol stubs.
`SIMPLE_NO_STUB_FALLBACK=1` correctly turns the full MCP package build into a
hard failure on those unresolved symbols, so stub cleanup remains tracked.

Current wrapper behavior: `bin/simple_mcp_server` probes native candidates in
order and only selects a candidate that returns the required WM text tools. It
prefers the passing `build/bootstrap/mcp-package/simple_mcp_server` when that
artifact exists, logs `native_probe_failed ... fallback=next_candidate` for any
stale native candidate, and only then falls back to
`bin/simple src/app/mcp/main.spl`. `bin/simple_lsp_mcp_server` now applies the
same checked-native selection and verifies `lsp_definition` before executing a
candidate.

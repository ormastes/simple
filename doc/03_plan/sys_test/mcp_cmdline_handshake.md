# MCP Command-Line Handshake Test Plan

## Scope

Validate the pure-Simple MCP server by building the exact native entry with
fresh pure Stage 2, launching it as a command-line process, sending an MCP
initialize/initialized/tools-list handshake, and requiring a bounded response.
Bootstrap acceptance also launches the exact Stage 5 MCP/LSP output pair once
before deploy; compiler Stages 2 through 4 do not duplicate the probe.

## Helper Contract

The system spec helper builds JSONL MCP messages, writes them to a temporary
stdin file, launches the exact native artifact, and verifies:
- `--json` readiness contains the expected server marker.
- Command exits with status `0`.
- Elapsed time is under `15000 ms`.
- Output contains JSON-RPC initialize and tools/list responses.
- Output contains a representative expected tool marker.
- Output does not report parse errors or native-missing failures.
- Feature responses preserve request IDs, contain semantic results, and contain
  neither JSON-RPC errors nor MCP `isError` results.

The helper is pure Simple spec code using stdlib process, file, env, and time
helpers. It must not declare direct `rt_*` externs and must not require Node.js.

The scenario executes the exact
`build/bootstrap/mcp-package/simple_mcp_server` artifact directly. It exercises
`simple_pipe` readiness and the bounded no-match behavior of `simple_search`;
a source-mode or Rust bootstrap warning fails the scenario. The wrapper-template
contract separately requires cached-native default execution and explicit-only
pure-Simple source fallback.

## Pass Criteria

The freshly built exact artifact answers the handshake within the time limit,
lists tools, and serves both representative feature calls.
The Stage 5 gate additionally requires successful `simple_status` and
`lsp_symbols` calls from the exact freshly built pair. `--no-mcp` is an explicit
skip and supplies no MCP acceptance evidence.

## Current Risk

Native artifact health is part of the contract. If the pure Stage 2 build fails
or the child process segfaults, the system spec fails; that is a server/package
bug, not a test-helper pass.

## Execution

```bash
# Prerequisite: fresh pure Stage 2 and Stage 3 (the SSpec performs the strict
# exact-entry MCP native-build itself).
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --pure-simple --no-mcp --jobs=half
bin/simple check test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl
bin/simple test test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl --native
```

## Traceability

| REQ | Description | Test File | Generated Spec | Coverage |
|-----|-------------|-----------|----------------|----------|
| REQ-MCP-CMD-001 | A pure-Stage2-built native Simple MCP answers initialize/tools-list and serves core tool calls within a time limit | `test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl` | `doc/06_spec/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md` | Full |
| REQ-MCP-CMD-002 | Fresh Stage 5 MCP/LSP outputs answer correlated handshakes and successful `simple_status`/`lsp_symbols` calls before deploy | `scripts/check/check-mcp-native-smoke.shs` | `doc/07_guide/tooling/mcp_handshake_regression.md` | Implementation complete; execution evidence pending pure-Simple CLI repair |

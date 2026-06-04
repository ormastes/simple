---
id: selfhosted_mcp_binary_segfault_2026-06-02
status: OPEN
severity: high
discovered: 2026-06-02
discovered_by: MCP server smoke test (initialize JSON-RPC)
related: bin/release/linux-x86_64/simple_mcp_server
related: src/app/mcp/main.spl
---

# Self-hosted simple_mcp_server binary segfaults on initialize

## Summary

The self-hosted compiled `bin/release/linux-x86_64/simple_mcp_server` (1.7MB,
built Jun 2 via native compilation) segfaults (exit 139) on any JSON-RPC
initialize request. The Rust-compiled `bin/release/x86_64-unknown-linux-gnu/
simple_mcp_server` (399KB, May 24) works correctly.

## Reproduction

```sh
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{...}}' | \
  bin/release/linux-x86_64/simple_mcp_server
# Exit 139 — Segmentation fault
```

## Impact

The `bin/simple_mcp_server` wrapper prefers `linux-x86_64/` over
`x86_64-unknown-linux-gnu/`. When the self-hosted binary exists, MCP is broken.

## Workaround

Remove the broken artifact: `rm bin/release/linux-x86_64/simple_mcp_server`.
The wrapper falls back to the working Rust-compiled binary.

## Root Cause (suspected)

Related to commit 1cd1c652 "unblock MCP native rebuild". The self-hosted
native compilation pipeline produces a binary that crashes on startup.
Likely a codegen or linker issue in the self-hosted compiler's native build.

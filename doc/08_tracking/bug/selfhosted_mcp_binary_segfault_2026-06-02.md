---
id: selfhosted_mcp_binary_segfault_2026-06-02
status: CLOSED
severity: high
discovered: 2026-06-02
discovered_by: MCP server smoke test (initialize JSON-RPC)
closed: 2026-06-12
closed_by: stage4 self-hosted deploy + workaround already applied
related: bin/release/linux-x86_64/simple_mcp_server
related: src/app/mcp/main.spl
---

# Self-hosted simple_mcp_server binary segfaults on initialize

## Summary

The self-hosted compiled `bin/release/linux-x86_64/simple_mcp_server` (1.7MB,
built Jun 2 via native compilation) segfaulted (exit 139) on any JSON-RPC
initialize request. The Rust-compiled `bin/release/x86_64-unknown-linux-gnu/
simple_mcp_server` (399KB, May 24) worked correctly.

## Reproduction (historical)

```sh
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{...}}' | \
  bin/release/linux-x86_64/simple_mcp_server
# Exit 139 — Segmentation fault
```

## Impact

The `bin/simple_mcp_server` wrapper prefers `linux-x86_64/` over
`x86_64-unknown-linux-gnu/`. When the self-hosted binary existed, MCP was
broken.

## Workaround (applied)

The broken artifact was removed: `bin/release/linux-x86_64/simple_mcp_server`
is absent. The wrapper now falls through to `build/bootstrap/mcp-package/
simple_mcp_server` (1.7MB, Jun 9 02:04, stripped ELF) which passes the
initialize + tools/list probe and responds correctly.

## Root Cause (suspected)

Related to commit 1cd1c652 "unblock MCP native rebuild". The self-hosted
native compilation pipeline at that point produced a binary that crashed on
startup — likely a codegen or linker issue in the pre-stage4 compiler.

## Closure — 2026-06-12

Re-verified after stage4 self-hosted deploy (bin/simple = 16 MB stage4 ELF,
deployed 2026-06-11 15:32, commit d36ad61714).

**Repro does not reproduce.** The broken binary
`bin/release/linux-x86_64/simple_mcp_server` is absent (workaround was
applied at some point between 2026-06-02 and 2026-06-12). The wrapper now
selects `build/bootstrap/mcp-package/simple_mcp_server` via the probe-stamp
cache and operates correctly.

Verification commands run 2026-06-12:

```sh
# 1. Broken binary is gone
ls bin/release/linux-x86_64/simple_mcp_server
# => ls: cannot access ... No such file or directory

# 2. Wrapper resolves to bootstrap/mcp-package binary
# (from .simple/logs/simple_mcp_startup.log):
# startup wrapper=simple_mcp_server mode=native \
#   native=.../build/bootstrap/mcp-package/simple_mcp_server

# 3. End-to-end MCP probe passes (exit 0, play_wm_text_status present):
printf '{"jsonrpc":"2.0","id":"1","method":"initialize",...}\n{"jsonrpc":"2.0","id":"2","method":"tools/list",...}\n' \
  | setsid timeout 8 bin/simple_mcp_server
# => exit 0, tools/list contains play_wm_text_status
```

The stage4 deploy changed `bin/simple` (the compiler CLI) to the self-hosted
binary, but the MCP _server_ binary itself (`simple_mcp_server`) is a
separately compiled artifact — it was not rebuilt by the stage4 deploy. The
effective fix here is the workaround (removal of the broken artifact), not a
stage4 codegen fix. If the MCP server is rebuilt natively again via the new
stage4 compiler, a new smoke test should be run before deploying.

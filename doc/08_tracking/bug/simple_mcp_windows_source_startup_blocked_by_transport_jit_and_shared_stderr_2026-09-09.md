# Simple MCP Windows source startup is not concurrency-safe and cannot be verified

Status: OPEN
Date: 2026-09-09
Platform: Windows 11, MSYS2 Bash 5.3.15, pacman 6.1.0

## Summary

Codex launches `bin\simple_mcp_server.cmd`, but the deployed Windows tree has
`simple_mcp_server.exe.disabled` instead of an admitted native server. The
generated source wrapper then runs `src/app/mcp/main.spl` and redirects stderr
to the process-global `%TEMP%\simple_mcp_server.err`.

Two independent blockers were reproduced:

1. A second MCP instance exits with `The process cannot access the file because
   it is being used by another process` because both wrappers truncate the same
   stderr file.
2. Source startup co-compiles unused generic transport helpers through
   `std.mcp_sdk.server.app`. Windows JIT rejects `transport_send.write_message`
   and `mcp_serve.read_message` as ambiguous, falls back to the interpreter,
   and the `stdin_read_char` serve loop returns no JSON-RPC initialize response.

This is unrelated to GitHub CLI, MSYS2/pacman installation, or `.bashrc`
aliases. A CMD byte-stable JSONL input returned a correct initialize response
after temporarily separating JSON field extraction from the server/transport
module, which confirms the dependency boundary as the likely code fix.

## Reproduction

1. Ensure no admitted `bin/release/x86_64-pc-windows-msvc/simple_mcp_server.exe`
   exists and the generated `.cmd` source wrapper is present.
2. Start one `bin\simple_mcp_server.cmd` process and keep stdin open.
3. Start a second instance; observe the locked temp-file error.
4. Run one instance with a JSONL `initialize` request; inspect stderr for
   `CODEGEN-AMBIGUOUS-METHOD` on `transport_send` and `mcp_serve`, followed by
   JIT fallback and no protocol response.

## Suggested resolution

1. Move `app_extract_id`, `app_extract_str`, and `app_extract_obj` into a
   transport-free `std.mcp_sdk.core.json_fields` module. Re-export them from
   `server.app` for compatibility, but import the core module directly from
   `src/app/mcp/main.spl` and remove its unused `mcp_server_init` call.
2. Add a Windows regression that starts two MCP wrappers concurrently and
   requires valid initialize responses from both. Never redirect all instances
   to one truncating temp path; inherit stderr or use a per-process path.
3. In a full isolated worktree, create the missing Stage 2 trust root with:
   `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --mode=dynload --output=<isolated-output>`.
   The sparse worktree must include
   `doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn` and
   `src/compositions/kernel_llvm_cranelift/compiler/driver/bootstrap_k1_selected.spl`.
4. Use the resulting hash/provenance/sanity receipts to build a fresh native
   MCP artifact, then run the core compiler/lib/MCP/LSP checks and
   `mcp_stdio_integration_spec.spl`. Do not certify with the deployed Rust seed
   or the unreceipted old `build/bootstrap/full` binary.

## Evidence from this investigation

- GitHub CLI upgraded successfully to 2.100.0.
- MSYS2 core upgrade completed; Bash reports 5.3.15.
- The deployed `bin/simple.exe` identifies itself as a Rust bootstrap seed.
- `build/bootstrap/full/x86_64-pc-windows-msvc/simple.exe` reports Simple
  v0.9.6 but has no adjacent admission/provenance receipt.
- The canonical Stage 2 trust-root attempt correctly failed closed when sparse
  policy/composition authorities were absent; no untrusted binary was used for
  release verification.

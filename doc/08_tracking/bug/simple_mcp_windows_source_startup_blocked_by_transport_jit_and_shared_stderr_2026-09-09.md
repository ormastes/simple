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

## Verdict on `simple_mcp_server.exe.disabled` (measured 2026-09-13)

Question asked: should the disabled April artifact be re-enabled (renamed back
to `.exe`) or rebuilt? **Rebuilt. Do not re-enable it.**

Measured directly on the artifact
(`bin/release/x86_64-pc-windows-msvc/simple_mcp_server.exe.disabled`,
dated 2026-04-23, 2,657,280 bytes):

| probe | result |
|---|---|
| `--version` under a 30s timeout | rc=124 (timed out), **no output at all** |
| MCP `initialize` frame on stdin, 30s timeout | no bytes on stdout |

It does not answer `--version`, which is the cheapest possible liveness probe,
so it cannot answer a handshake either. Renaming it to `.exe` would make the
`.cmd` prefer a **hanging** binary over the slow-but-working source fallback —
strictly worse than the present state, and it would hang Codex/Claude MCP
startup rather than merely making it slow.

Two independent reasons a rebuild is required rather than a rename:

1. It is a hung binary, per the measurement above.
2. Even a working artifact would still be rejected by the generated sh wrapper:
   `native_hash_is_valid` requires a `<binary>.sha256` sidecar and **no
   `.sha256` sidecar exists anywhere in
   `bin/release/x86_64-pc-windows-msvc/`**. That is the reason the Jun-1
   `simple_lsp_mcp_server.exe` in the same directory is also skipped: it is
   host-compatible (verified PE, `simple_host_executable_compatible` returns
   true) and is named in the candidate list, and is rejected purely for the
   missing sidecar. A rebuild must therefore emit the sidecar alongside the
   binary.

The file is deliberately left in place, renamed to nothing and deleted by
nothing: it is the only record of what the April artifact was, and deleting it
would not produce a working server.

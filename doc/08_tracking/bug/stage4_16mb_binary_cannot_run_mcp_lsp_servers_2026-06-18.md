# Bug: deployed stage-4 (~16MB) bin/simple cannot run MCP/LSP server programs

- **Filed:** 2026-06-18
- **Severity:** P1 (source-mode simple-mcp + simple-lsp-mcp non-functional for fresh spawns)
- **Components:** bootstrap (stage-4 seed+cranelift), interpreter large-program execution, `bin/simple run`

## Symptom

The currently-deployed `bin/release/x86_64-unknown-linux-gnu/simple` is a ~16MB
stage-4 (seed+cranelift) build. It runs small programs fine but **silently fails
to run the large MCP/LSP server programs** — it emits no output at all (not even
the JSON-RPC `initialize` response):

```sh
SIMPLE_LIB=$PWD/src bin/simple run src/app/mcp/main.spl            # → (empty), exit 0
SIMPLE_LIB=$PWD/src bin/simple run src/app/simple_lsp_mcp/main.spl # → (empty), exit 0
```

Working baseline (small programs) on the same binary:

```sh
bin/simple -c 'print(1+1)'        # → 2
bin/simple run /tmp/trivial.spl   # → prints
bin/simple lint /tmp/trivial.spl  # → OK (no coredump)
```

stderr during the failed server runs shows only benign WARNs (these also appeared
on the previously-working ~461MB binary, so they are **not** the cause):

```
WARN ... Export statement references undefined symbol name=rt_file_write_text
WARN ... Export statement references undefined symbol name=rt_file_read_text
[memory-guard] SIMPLE_LIB=... contains 600+ .spl files
```

## Impact

All source-mode MCP wiring launches servers via `bin/simple run <server>.spl`
(see the install.shs / wrapper / template changes from the 2026-06-18 MCP work).
With this binary, **simple-mcp and simple-lsp-mcp produce nothing on a fresh
spawn** → both MCP servers are non-functional for any newly-started client.
Live in-session connections that were spawned against the prior ~461MB compiler
keep working until they are restarted/reconnected.

It also blocks deploying the `rt_process_run` deadlock fix
(`9c28cec`, see `lsp_mcp_native_arg_extract_and_source_diagnostics_deadlock_2026-06-18.md`):
the fix is correct and compiled into the rebuilt runtime, but a stage-4 binary
that can't run the LSP server can't exercise it.

## Root cause

`bootstrap-from-scratch.sh` (even with `--backend=llvm-lib`,
`LLVM_SYS_180_PREFIX=/usr/lib/llvm-18`) cannot self-host: **stage-3 fails**
(LIM-010, LLVM symbol conflicts — "stage2 binary cannot recompile itself"), so
stage-4 falls back to the **seed + cranelift** path. That stage-4 binary
miscompiles / cannot execute large full programs (the MCP/LSP servers), even
though `-c`/lint/small runs succeed. The previously-deployed ~461MB binary was an
LLVM-built compiler that *could* run them; it was replaced by a parallel session's
~16MB stage-4 deploy on 2026-06-18 ~03:07.

See `project_bootstrap_stage3_selfhost_broken` and
`mcp_full_program_native_codegen_and_arg_extract_2026-06-16.md`.

## Repro

```sh
# Confirm small programs work but the servers do not:
SIMPLE_LIB=$PWD/src
printf 'fn main()->i64:\n    print("ok")\n    0\n' > /tmp/t.spl
bin/simple run /tmp/t.spl                                    # prints "ok"
printf '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"p","version":"0"}}}\n' \
  | timeout 60 bin/simple run src/app/mcp/main.spl           # → EMPTY (bug)
```

## Fix options

1. **LLVM native-build route** — build the full CLI via
   `simple compile --native --backend llvm` of `src/app/cli/main.spl` (the
   ~461MB-class capable binary) and deploy that. Blocker tracked in
   `mcp_full_program_native_codegen_and_arg_extract_2026-06-16.md` (folded builtin
   string methods in LLVM `MethodCallStatic`).
2. **Fix stage-3 self-host (LIM-010)** so the bootstrap produces a self-hosted
   stage-4 capable of large programs.

Either makes `bin/simple run` execute the MCP/LSP servers again; at that point the
`rt_process_run` fix takes effect and the `SIMPLE_LSP_ENABLE_DIAGNOSTICS` gate can
be removed.

## Notes

- A parallel session's deploy replaced `bin/simple` mid-investigation; the
  prior 461MB binary and its `.pre_deploy` sibling are gone. Backup of the current
  16MB binary: `/tmp/simple.working.backup`.
- `bin/simple` was NOT modified by this investigation (no `--deploy` was used).

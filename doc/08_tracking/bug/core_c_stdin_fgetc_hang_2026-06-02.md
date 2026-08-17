# core-c MCP stdin hang — C runtime stdin_read_char uses fgetc (2026-06-02) — FIXED (worked around)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Summary

On the macOS ARM64 **core-c** native lane, the MCP/LSP/serial stdio servers
hung forever instead of reading a request. Root cause: the C runtime's
`stdin_read_char` (`src/runtime/runtime_native.c`) uses buffered stdio
(`fgetc`), and the minimal core-c link leaves `fgetc`/`fgets` unresolved →
weak-stubbed → returns garbage that never signals EOF, so the Simple read loop
(`_read_line`: `while ch != ""`) spins forever.

`read()`/`write()` (raw syscalls) link and work correctly on core-c; only the C
buffered-stdio entry points are missing.

## Repro (before fix)

```
printf '' | <core-c mcp binary>   # hangs (timeout), no output
```
A bare-`read` probe confirmed `read(0, buf, 1)` returns `0` at EOF correctly,
isolating the fault to `fgetc`-based `stdin_read_char`.

## Fix applied (pure Simple)

`src/app/mcp/main_lazy_protocol.spl` now reads stdin with a pure-Simple
`mcp_read_char()` that calls the `read()` syscall directly (mirroring
`simple_core`), bypassing the C `fgetc` path entirely — no C edits, no symbol
duplication. After the fix the MCP server reads input correctly and terminates
cleanly on EOF (verified).

This unblocks reading; the MCP still cannot respond on core-c due to the
separate `.len()` bug — see `core_c_string_len_registry_2026-06-02.md`.

## Proper long-term fix

Same as the `.len()` bug: migrate the core-c lane runtime to pure-Simple
`simple_core` (whose `stdin_read_char` already uses `read()`), so the C
`fgetc` version is no longer linked anywhere. See
`mcp_simple_core_runtime_migration_2026-06-02.md`. The shared LSP/serial
`json_helpers.spl` still uses the C `stdin_read_char`; it works in the
interpreter and rust-hosted lanes but would need the same treatment for a
core-c deploy.

## Related

- `core_c_string_len_registry_2026-06-02.md`
- `mcp_redeploy_smoke_failures_2026-06-01.md`

## 2026-08-17 verification — runtime lane

**Verdict: STILL OPEN. Workaround confirmed in place; proper fix is out of this lane's scope.**

The immediate MCP hang remains worked around in `main_lazy_protocol.spl`, and the
doc's "Proper long-term fix" section is still unimplemented: `json_helpers.spl`
continues to use the C `fgetc`-based `stdin_read_char`. Both of those files are
under `src/lib/**` / `src/app/**`, outside this lane's `src/runtime/**` scope, so
no edit was made.

**What was NOT proven.** No reproduction was attempted — the row carries
`reproducible_by: NONE` and no runnable reproducer exists in the doc. This entry
records scope, not evidence of behaviour.

## 2026-08-17 verification — runtime slice (classified by CONTENT)

**Verdict: STILL OPEN.** The C `fgetc`-based primitive is unchanged in current
source, `src/runtime/runtime_native.c:2119-2125`:

```c
int64_t stdin_read_char(void) {
    int ch = fgetc(stdin);
    if (ch == EOF) return rt_string_new(NULL, 0);
    uint8_t byte = (uint8_t)ch;
    return rt_string_new(&byte, 1);
}
```

The doc's "Proper long-term fix" is therefore still unimplemented. Seven owned
`.spl` consumers still call the extern: `src/lib/nogc_sync_mut/lsp/lsp_protocol.spl`,
`src/lib/nogc_sync_mut/mcp_sdk/transport/{stdio,transport}.spl`,
`src/lib/nogc_async_mut/mcp/{protocol,lazy_protocol_io,fileio_main}.spl`,
`src/lib/nogc_async_mut/host_io/stdio.spl` (plus `src/compiler/90.tools/fix/main.spl`).

**Doc metadata correction:** the row/doc names `json_helpers.spl` as the holdout
caller. No `json_helpers.spl` exists anywhere under `src/` in current source — that
filename is stale; the live callers are the list above.

**What was NOT proven.** No hang was reproduced or excluded by execution: this is
C-runtime code reachable only from a NATIVE-compiled binary, and `bin/simple` is
the Rust seed using the Rust runtime, so an interpreted probe would be vacuous.

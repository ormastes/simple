# core-c MCP stdin hang — C runtime stdin_read_char uses fgetc (2026-06-02) — FIXED (worked around)

Status: FIXED on release/1.0.0 (verified 2026-11-09) — see addendum below

## 2026-11-09 verification — fixed on release/1.0.0

- **measured** `src/runtime/runtime_native.c:3955-3960` `stdin_read_char` no
  longer uses `fgetc`; it reads via `stdin_raw_byte` (raw `read(0, buf, 1)`,
  EINTR-retried), and all four stdin readers share that raw fd-0 byte reader.
- **measured** fixing commits `ea2afa2f689` ("stdin_read_char uses raw read(0)
  instead of fgetc") and `1b7d3a320e2` ("route all four stdin readers through
  one raw fd-0 byte reader") are ancestors of `origin/release/1.0.0`.
- **measured** host C repro (`build/p3-stdin-repro` in worktree
  `build/agent-worktrees/p3-stdin`): RED — the old `fgetc`-based loop under
  weak-stub semantics (never EOF) spins forever, killed by a 5 s watchdog
  (exit 124). GREEN — functions extracted live from `runtime_native.c` deliver
  pipe bytes then return the empty string at EOF, so the
  `while ch != ""` loop terminates; in-tree
  `src/runtime/test/rt_stdin_read_char_raw_selfcheck.c` PASS;
  `cc -fsyntax-only runtime_native.c` clean.
- **not verified here** the original macOS ARM64 core-c minimal-link
  reproduction (no macOS host); the weak-stub failure mode is simulated at the
  C level. `json_helpers.spl` still calls the C `stdin_read_char`, which is
  now the raw-read implementation.

## Re-triage 2026-09-13 — reopened: the pure-Simple `mcp_read_char()` workaround is absent

- **measured** `grep -rn 'mcp_read_char' src/` returns nothing; the fix this entry
  claims was applied to `src/app/mcp/main_lazy_protocol.spl` does not exist there
  (that file has no stdin read path at all today).
- **measured** `src/app/mcp/main.spl:251-259` still defines `_mcp_read_line()` as a
  `while true` loop over `stdin_read_char()`, i.e. the exact loop shape the entry
  says spins forever on core-c.
- **measured** `src/runtime/runtime_native.c:2626-2633` still implements
  `stdin_read_char` with `fgetc(stdin)` — the reported root cause is unchanged.
- **inferred** The hang itself is specific to the macOS ARM64 core-c minimal link
  (where `fgetc` is weak-stubbed); no macOS host is available here, so this is
  reopened on missing-fix evidence, not on a fresh reproduction.

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

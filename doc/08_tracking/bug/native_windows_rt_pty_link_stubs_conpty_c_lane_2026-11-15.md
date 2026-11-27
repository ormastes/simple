# Native Windows builds stubbed rt_pty_open/spawn/read/write/close (2026-11-15)

Status: verification-pending

## Symptom
A native Windows build (`native-build`, core-C runtime lane) listed
`rt_pty_open`, `rt_pty_spawn`, `rt_pty_read`, `rt_pty_write`, `rt_pty_close` in
`<exe>.stubbed_symbols.txt`, and the first PTY call aborted:
`fatal: called unresolved symbol rt_pty_open (stubbed for link only)` (seen in
the 2026-11-14 native llm_caret smux owner measurements, PR #9224).

## Root cause
The ConPTY implementation existed only in the Rust runtime
(`src/compiler_rust/runtime/src/value/pty.rs`, `#[cfg(windows)] mod pty_process`).
The C runtime that native builds link had no open/spawn/read/write/close, and
its Windows `rt_pty_is_running` / `rt_pty_resize` answered a fixed `false`.

## Fix
`src/runtime/runtime_process.c` gains a Windows ConPTY lane that mirrors the
Rust lane (pipes, `CreatePseudoConsole` flags, `CreateProcessW` command line,
`PeekNamedPipe` polled read with a held-back UTF-8 tail, terminate ->
`ClosePseudoConsole` -> close teardown). It uses a lockless CAS-claimed slot
table with use counts, and handle generations so a reused slot does not answer a
stale handle. `text` crosses this ABI as a RuntimeValue string (`rt_string_data`/`rt_string_len`,
result via `rt_string_new`). Now-dual symbols removed from
`scripts/check/rt_dual_implementation_baseline.txt`.

Evidence: `test/02_integration/runtime/pty/fixture/conpty_echo_main.spl`, native-built.
- RED: `fatal: called unresolved symbol `rt_pty_open` (stubbed for link only)`, rc=127
- GREEN: `spawn_ok=true running=true write=true marker_seen=true exited=true close=true close_again=true`, rc=0

## Not covered / follow-ups (Windows caret BLOCKED specs)
- POSIX C lane still has no open/spawn/read/write/close (unchanged scope).
- `rt_pty_spawn_exec_v1`, `rt_pty_write_bytes_v1`, and `rt_pty_exit_code_v1` stay unsupported on Windows in both lanes, the same as before.
- **smux socket specs** (`smux_runtime_*`, `smux_signed_binding_socket`,
  `smux_owned_terminal_transport`, the `PLATFORM SKIP os=linux` socket specs):
  they need the 18 `rt_local_unix_*_v1` symbols, which
  `src/runtime/runtime_socket_nonblock.c` defines only under `!_WIN32`. Porting
  them means Windows AF_UNIX (afunix.h, Win10 1803+) with matching peer
  credential and handoff semantics. That is a multi-day port, not a small gap.
- **llm_caret_tui_pty**: `scripts/check/check-llm-caret-tui-pty.shs` (1203
  lines) relies on `script`, `stty -g`/`stty size` terminal-restoration checks,
  `pgrep`, and a cached `bin/release/<triple>/caret` with provenance. A port
  would rewrite the harness as a Simple driver over `std.sys.pty`, which is now
  usable natively on Windows. ConPTY has no `stty -g` equivalent, so the
  restoration case needs a redefined contract that the owner has to approve. Plan only.
- **tmux specs** (`caret_agent_infra_acceptance_spec`): the contract is about
  tmux itself (the private tmux server's exit status, panes read "without leaving
  tmux"). Swapping in smux would change the spec contract, so it was not done.

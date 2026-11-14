# std.sys.terminal_console has no Unix provider (2026-11-14)

**Status:** provider landed on `work/smux-native-fixtures-20261114`; one named
gap remains (non-blocking read). `smux_literal_input_spec.spl` is still 0/3
because its compiled child cannot be provisioned yet (see
`smux_native_fixture_children_never_provisioned_2026-11-14.md`).

## Symptom
`test/fixtures/coremux/literal_input_child.spl` calls
`std.sys.terminal_console.open()`, which returned
`Err("interactive console provider unavailable in this runtime composition")`
on every host, so the child exited 22 before `LITERAL_CHILD_READY`.

## Root cause
`src/lib/sys/terminal_console.spl` was a refusing stub; no Unix provider was
composed although the runtime already owns the primitives
(`rt_terminal_enable_raw_mode`/`disable` = cfmakeraw + saved-termios restore,
`rt_terminal_is_tty`, `rt_terminal_get_size`, `rt_stdin_read`, `rt_term_write`,
`rt_term_flush`).

## Fix
Pure-Simple Unix provider in `src/lib/sys/terminal_console.spl`: one exclusive
owner handle; `open()` requires tty stdin and enters raw mode; `close()` /
`cleanup()` restore termios; foreign handles refused. Windows still refuses.

## Evidence
- Before: child under `script(1)` pty exits 22, no ready line.
- After: `bin/simple run test/fixtures/coremux/literal_input_child.spl literal`
  under `script -q` prints `LITERAL_CHILD_READY` (seed
  `release100-pty-structured-20261114`).
- Generalization spec `test/01_unit/lib/sys_terminal_console_unix_provider_spec.spl`:
  `outcome=OK passed=2`.
- Reproducer `test/03_system/tools/smux_literal_input_spec.spl`: still 0/3 —
  blocked on the compiled child, not on the provider.

## Open gap (named, not filled)
`read()` blocks until >=1 byte: cfmakeraw leaves VMIN=1/VTIME=0 and no runtime
extern exposes non-blocking/poll on fd 0 (`rt_io_tcp_set_nonblocking` only
covers socket-registry handles). `src/os/apps/smux/interactive_client.spl:327`
polls `console_read` in a heartbeat loop and needs a non-blocking read.
Unblock: add `rt_stdin_poll_v1(timeout_ms)` (or VMIN=0/VTIME=n raw variant) in
both runtime lanes and use it in `read()`.

# Unix rt_pty_close not idempotent; closed raw fd numbers (2026-11-15)

**Status:** FIXED (branch `work/pty-close-idempotent-20261115`)

## Symptom
`test/03_system/tools/smux_configured_launch_spec.spl` case "publishes a real
configured child through the public API and preserves it across client detach"
failed: after `smux_kill_session` (which already closes the pane PTY via
`close_owned_children`, `src/os/apps/smux/child_lifecycle.spl:94`), the spec's
`configured_api_close_tokens` re-closes each handle and expects idempotent
success. Unix `native_pty_close` did `libc::close(fd)` unconditionally -> EBADF
-> `false` forever.

## Root cause / hazard
Close acted on a raw fd number with no ownership check. Besides the false
result, a second close could close an unrelated file that reused the number.

## Fix
`src/compiler_rust/runtime/src/value/pty.rs`: `PTY_OWNED_FDS` set,
`note_pty_owned` on every open path (`pty_process::open`, both ends from
`native_pty_openpty`, interpreter `pty_open`), `take_pty_owned` in
`native_pty_close` and interpreter `pty_close`. An fd not owned returns `true`
without calling `libc::close`. Windows `pty_process::close` on an unknown
handle now also returns `true` (handles are table keys, so no reuse hazard).

## Tests
Rust: `rt_pty_close_is_idempotent`, `rt_pty_close_leaves_unowned_fd_open`
(pipe fds stay open). Interpreter invalid-handle test now expects `true`.

## BSD
Same `libc::openpty`/`close` path on FreeBSD/OpenBSD/NetBSD; the set is
platform-neutral, so behaviour is identical (reasoned, not VM-run).

# SimpleOS PTY provider lacked 11 facade ops; host-capability spec contradicted idempotent close

**Status:** FIXED (branch `work/pty-common-interface-20261122`)
**Found:** 2026-11-22, PTY common-interface parity audit (Windows 11 host)

## Common interface

`std.sys.pty` (`src/lib/sys/pty.spl`) is the PTY contract. Both SOSIX facades
(`src/lib/nogc_sync_mut/sosix/pty.spl`, `src/lib/nogc_async_mut/sosix/pty.spl`)
are pure `export use` aliases of its 17 operations plus the shell kinds and
`PtyLaunchV1` types. Every smux/caret caller imports through `std.sosix.pty`; no
`src/app` or `src/os` caller reaches `rt_pty_*` or `windows_pty_owner` directly.
Providers: the Rust-runtime `rt_pty_*` lane (Unix + Windows ConPTY,
`src/compiler_rust/runtime/src/value/pty.rs`), the Windows native overlay
(`src/providers/windows_native/lib/sys/pty.spl` -> `windows_pty_owner.spl`),
and SimpleOS (`src/os/apps/shell/pty_provider.spl`).

## Defect 1: SimpleOS provider was a partial surface

`src/os/apps/shell/pty_provider.spl:73` exported only `open, spawn, spawn_v1,
write, read, is_running, close, platform_default_shell`. Missing:
`spawn_configured_v1, configured_launch_probe_v1, literal_bytes_supported_v1,
write_literal_some_v1, write_some, input_pending, hangup, can_resize, resize,
cleanup_pending, exit_code` and the `PtyLaunch*` re-export. smux calls
`write_some`/`input_pending`/`cleanup_pending`/literal ops
(`src/os/apps/smux/pane_io_service.spl:22-28`) and `can_resize`/`resize`
(`window_layout_service.spl:9`), so selecting this provider would fail.

Fix: each missing op is present and refuses explicitly (`can_resize`/`resize`/
`hangup` false, `exit_code`/`spawn_configured_v1`/`write_literal_some_v1` Err,
`input_pending` Ok(false), `cleanup_pending` 0, `write_some` via
`pty_input_prefix` + `write`, the same fallback `std.sys.pty` uses).

## Defect 2: close semantics

`rt_pty_close` is idempotent since `ec155bf6bc9` (2026-11-15; Rust tests
`rt_pty_close_is_idempotent*` assert true twice on Unix and Windows) and
`windows_pty_close_v1` answers its cleanup proof (true) for a closed slot. The
SimpleOS provider returned false on a second close, and
`test/01_unit/os/tty/pty_host_capability_spec.spl:52` still asserted `false`
(written 2026-09-29, before the contract changed) - its only failing example
on Windows; the live round trip itself passed. Fix: SimpleOS close answers true
for any handle it issued; the spec asserts the idempotent contract.

## Specs

- Reproducing: `test/01_unit/os/apps/shell/pty_provider_spec.spl` - "refuses the
  host-only operations explicitly" calls every facade op on the provider (a
  removed op fails it; verified by renaming `exit_code`, 3/4 -> red) and
  "closes idempotently like the host providers".
- Generalization: `test/01_unit/os/tty/pty_host_capability_spec.spl` - the
  host provider's double close, now asserting the shared contract.

Phase 1 interpreter (pinned-ac2e90625c2a) on Windows 11: 4/4 and 4/4.
SimpleOS guest/board run remains open:
`doc/08_tracking/todo/simpleos_pty_provider_unverified_2026-11-14.md`.

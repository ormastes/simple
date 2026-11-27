# Windows portable PTY lane refuses exit_code; structured launch and literal bytes too

**Status:** OPEN (needs a Rust seed change; not fixed while a bootstrap is running)
**Found:** 2026-11-22, PTY common-interface parity audit (Windows 11 host)

## Symptom

On Windows under the Rust-runtime lane (interpreter / seed products), a ConPTY
child that exits with `exit 7` reports:

```
running_after_exit=false
exit_code_err=PTY exit status unavailable in this runtime composition
```

The Unix lane returns the code (or 128+signal) and the Windows native overlay
(`src/providers/windows_native/lib/sys/pty.spl` -> `windows_pty_exit_code_v1`,
`src/lib/nogc_sync_mut/io/windows_pty_owner.spl:536`) returns it from the
retained process handle. So `std.sys.pty.exit_code` parity on Windows depends on
which provider is composed.

## Cause

- `src/lib/sys/pty.spl` `exit_code`, `spawn_configured_v1`,
  `write_literal_some_v1`, `literal_bytes_supported_v1`,
  `configured_launch_probe_v1` gate on `_pty_unix_host()`.
- `src/compiler_rust/runtime/src/value/pty.rs:1508-1521`
  (`rt_pty_exit_code_v1`) returns -2 off Unix, and `rt_pty_spawn_exec_v1` /
  `rt_pty_write_bytes_v1` (`:1449`, `:1481`) return -1 off Unix, although the
  Windows ConPTY arm of `pty_process` already retains the child process handle.

Documented as an explicit refusal in
`unix_pty_structured_launch_literal_bytes_exit_code_missing_2026-11-14.md`;
recorded here as the remaining Windows-lane parity gap. No current `.spl`
caller uses `sosix_pty_exit_code`, so smux is unaffected today (its exit status
round trip goes through the shell: `%ERRORLEVEL%`).

## Unblock

Implement `rt_pty_exit_code_v1` on the Windows `pty_process` arm
(`GetExitCodeProcess` on the retained handle, -1 while running), then drop the
`_pty_unix_host()` gate on `exit_code` only. Needs a seed rebuild; verify with
`test/01_unit/lib/sosix/pty_provider_alias_spec.spl` plus a live
`exit 7` -> `Ok(7)` probe on Windows.

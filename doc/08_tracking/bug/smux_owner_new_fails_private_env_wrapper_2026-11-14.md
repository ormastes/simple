# smux owner `new` fails: std.sys.pty_shell imports private env wrappers (2026-11-14)

Status: FIXED (branch work/smux-caret-live-fixes-20261114)

## Symptom
`test/01_unit/os/apps/smux/server_large_reply_drain_spec.spl` 0/2 on macOS: the
owner answered `list-sessions`, but `new big` returned `empty smux response`
and every later request `smux owner unavailable` (reply length 0).
Owner log: `error: semantic: private fn env_get_unchecked of module
src/lib/nogc_sync_mut/sffi/env.spl is not visible to src/lib/sys/pty_shell.spl`.

## Reproducer
```
bin/simple run src/app/hosted_apps/smux_client.spl --serve 127.0.0.1:39124 <32-hex token>
# then smux_server_request_within(addr, token, "new big", 30000)  -> Err("empty smux response")
```
Spec: `test/01_unit/lib/nogc_sync_mut/sffi/env_wrapper_visibility_spec.spl`
(red 1/2 before, 2/2 after).

## Root cause
`src/lib/sys/pty_shell.spl:12` (added with the shs default-shell change)
imports `env_get_unchecked`, `env_cwd_raw` — module-private `fn`s in
`src/lib/nogc_sync_mut/sffi/env.spl`. The current seed enforces visibility,
so resolving the default PTY shell (every session `new`) aborted the owner.

## Fix
`env.spl` exports `env_get_unchecked, env_cwd_raw, env_set_cwd_raw` — the
wrappers this file exists to give product code (header), and the set the tree
imports (`pty_shell`, `os.apps.shell.shell_host`, test runner).
Generalization: the second spec example imports all three directly.

## BSD
Platform-neutral (module visibility); FreeBSD hosts had the identical break.

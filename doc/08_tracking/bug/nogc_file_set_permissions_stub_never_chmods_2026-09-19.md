# `std.nogc_sync_mut.file_system.permissions.file_set_mode` never changes the mode

**Date:** 2026-09-19
**Found by:** linker lane A7 slice 2 review fix. Replacing `shell("chmod +x ...")` with
`file_set_mode(output, 493)` left the linked output non-executable, and
`link_engine_external_spec` went from 15/15 to 13/15.
**Severity:** silent wrong answer. The call returns `true` and does nothing.

## Where

`src/lib/nogc_sync_mut/file_system/permissions.spl`:
- `file_set_mode(path, mode)` calls `file_set_permissions(path, permission_from_mode(mode))`.
- `file_set_permissions` (~line 77) only checks `file_exists(path)` and returns `true`.

No syscall is made. The `gc_async_mut` twin declares `extern fn rt_file_set_mode`; the
`nogc_sync_mut` family never calls it.

## Impact

Every `nogc_sync_mut` caller that relies on it gets no mode change and a `true` result. Two
callers are `src/app/devhub/adapter_outlook_curl.spl:222` and
`src/app/itf/adapter_outlook_curl.spl:222`, which set the cache file mode, so those cache
files keep their default permissions.

## Fix direction

Back `file_set_permissions` with the real host call through the SOSIX host facade (per the
host-interface-only plan), or delegate to the `gc_async_mut` extern. Add a spec that stats
the mode after the call.

## Workaround in place

`src/compiler/70.backend/linker/link_engine_external.spl` uses
`process_run("chmod", ["755", output])`, which passes an argv array and needs no shell.

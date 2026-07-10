# BUG: @cfg multi-variant function mis-dispatch on x86_64-unknown-none native-build

**Status:** open
**Severity:** high (silently routes to the wrong architecture's implementation)
**Component:** compiler native-build `@cfg` resolution (Cranelift, `x86_64-unknown-none`)
**Found:** 2026-07-10 (during the SimpleOS SSH → ring-3 exec demo)

## Symptom

A function defined once per architecture via `@cfg(...)` (six same-named variants,
compiled as `<name>$dup0..dup5`) is called from a wrapper, and the WRONG variant is
selected on the `x86_64-unknown-none` build.

Two independent reproductions in `src/os/kernel/loader/fs_exec_spawn.spl`:

1. `_fs_exec_spawn_ring3_active` — the `@cfg(x86_64)` variant calls
   `x86_64_fs_exec_spawn` (FAT + ring-3 handoff). At runtime the wrapper
   `fs_exec_spawn_ring3` instead reached the `@cfg(x86)`/riscv variant that calls
   `fs_exec_spawn` → `fs_exec_spawn_as` → `g_vfs_read_executable_bytes`. Proof: the
   serial log shows `[vfs-read] …` (only reachable via `fs_exec_spawn_as`) while the
   intended `x86_64_fs_exec_spawn_as` (its unique `spawn:preloaded`/`preload-check`
   prints) is never hit.
2. A fresh helper `_fs_exec_spawn_ring3_preloaded_active` with the same 6-variant
   `@cfg` shape returned `-16` (a non-x86_64 stub body) instead of calling the
   `@cfg(x86_64)` body.

## Likely cause

`x86_64-unknown-none` appears to activate the `x86` cfg token (or otherwise fails to
uniquely pick `x86_64`) when multiple same-named `@cfg` variants exist, so the
caller binds to a non-`x86_64` `$dupN`. Not yet minimized to a compiler unit test.

## Workaround

Call the single, non-`@cfg`, `pub` target function directly (e.g.
`x86_64_fs_exec_spawn(...)`), bypassing the `@cfg` dispatch helper. Unambiguous
symbol → correct target. (Downside: caller must be arch-specialized or guarded.)

## Repro / fix pointer

Minimize: a wrapper calling a 6-`@cfg`-variant helper where the `x86_64` variant
calls fn A and another variant calls fn B; build `--target x86_64-unknown-none
--backend cranelift`; observe B runs. Fix in native-build `@cfg` token activation /
variant selection so `x86_64` targets bind the `@cfg(x86_64)` variant.

## Related

- `doc/08_tracking/bug/x64_ssh_kernel_fat32_stream_open_zero.md` (bug #4 there)

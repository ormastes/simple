# Scripted Windows Docker cooperative progress refuses under the seed on a Windows host

- **Status:** OPEN (2026-11-22) — spec left RED
- **Component:** `src/lib/nogc_sync_mut/io/windows_command_domain_v4.spl:10-16`
  (`windows_command_registry_thread_v4`), used by
  `src/lib/nogc_async_mut/container/providers/windows/docker_runtime_v1.spl:525-575`
  (`progress_begin_v2`, `progress_poll_v2`)
- **Found:** 2026-11-22, Phase 1 (seed `ac2e90625c2a`) run on Windows 11 (build 26300).

## Symptom

`test/01_unit/lib/nogc_async_mut/container/providers/windows/docker_server_network_v6_spec.spl:288`
"uses the same network stages in bounded cooperative progress" fails with
`expected blocked to equal ok`; the operation reason is
`windows-command-canonical-thread-required` at stage `engine` after 3 scripted replies.
22 of 23 examples pass. The non-Windows branch of `windows_command_registry_thread_v4`
admits scripted turns (code path; not executed here).

## Cause

On Windows, `windows_command_registry_thread_v4(scripted)` ignores `scripted` and always
calls `windows_command_thread_check_v2()`, which needs
`rt_windows_pty_owner_thread_guard_v1() == 1`. The Rust seed's runtime returns `0` by
design (`src/compiler_rust/runtime/src/value/sffi/process_environment_v1.rs:221`, "The
Rust lane has no shared native PTY owner-thread binding"). So a scripted provider, which
never touches a native command owner, still cannot poll progress under the seed on a
Windows host. The non-Windows branch admits `scripted`.

## Unblock condition

Owner decision: either (a) scripted progress on Windows skips the native thread guard as
on other hosts (scripted turns never enter the native registry), or (b) the requirement
is deliberate and this example must run only on a native core-C lane, in which case the
spec needs that host/runtime precondition stated. Until then the example stays RED on the
Windows seed lane.

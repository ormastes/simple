# Callerless VFS executable-read bypass

**Status:** Open — blocks SimpleOS enhancement AC-5 filesystem isolation

## Evidence

`src/os/kernel/loader/fs_exec_spawn.spl:218` now exposes the explicitly named
`fs_exec_read_boot_executable_bytes(path)` only for kernel-origin PID1 image
discovery. It delegates directly to the active global VFS reader because no
live caller context exists at that bootstrap point.

The former shell PATH consumer has been migrated: `shell_path_candidates()` is
now pure name construction and `shell_exec_as` attempts each candidate only
through the recipe-gated launch path. It advances only after a normal not-found
result; an authorization or image failure is returned immediately. This closes
the shell's direct global-read bypass, but the raw helper remains exposed for
boot and other future callerless consumers.

Boot reads in `src/os/kernel/boot/pid1_launch.spl` are a separate kernel-origin
bootstrap exception and must remain explicitly named as such.

## Required resolution

1. Add a context-aware executable lookup/read API which resolves an already
   canonical path only after `FileRead`/`FileExec` and isolation-domain checks.
2. ~~Thread a live `KernelCallContext` into PATH resolution and shell execution;
   remove shell access to `fs_exec_read_executable_bytes`.~~ **Partially
   resolved:** shell no longer reads global VFS; the legacy scalar recipe bridge
   still needs conversion to a live `KernelCallContext`/scheduler ABI.
3. ~~Rename or privatize the current raw helper as a boot-only reader and permit
   only kernel-origin boot call sites.~~ **Resolved:** it is now named
   `fs_exec_read_boot_executable_bytes` and PID1 is its sole consumer.
4. Migrate every userspace-request VFS operation, including open-by-FD,
   readdir, rename, links, mounts, and metadata, onto the same caller-aware
   isolation-domain path.
5. Add a cross-domain system test proving a shell/agent cannot discover or
   execute a peer-domain executable by PATH probing.

## Unblock evidence

Focused unit coverage must show context-less nonboot lookup is rejected and a
real caller can discover only a granted executable path. QEMU system evidence
must demonstrate cross-domain PATH denial.

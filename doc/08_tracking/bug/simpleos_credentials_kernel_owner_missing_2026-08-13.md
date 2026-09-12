# SimpleOS credential identity requires a kernel owner
**Status:** OPEN (unverified 2026-09-12)

## Status

Guest libc now fails closed; credential semantics remain unavailable.

## Fault and repair

The previous `getuid`, `getgid`, `geteuid`, and `getegid` facades returned
zero, falsely advertising root identity.  They now return their unsigned
all-bits-one sentinel and set `errno=ENOSYS` until a kernel credential owner
can provide process identities consistently to libc, VFS, process creation,
and stat metadata.

## Unblock condition

Add kernel-owned real/effective UID/GID state, capability checks, inheritance
through spawn/fork/exec, VFS metadata enforcement, and target-side regressions.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

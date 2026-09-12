# SimpleOS epoll_pwait signal-mask false success
**Status:** OPEN (unverified 2026-09-12)

## Status

Mitigated: non-null masks are honestly rejected.

## Defect

`epoll_pwait` discarded its signal mask and delegated to `epoll_wait`, while
returning the ordinary readiness result. That advertised an atomic
mask-installation-and-wait transition that the SimpleOS signal facade cannot
provide, reopening critical signal-delivery races.

## Current boundary

`epoll_pwait(..., NULL)` remains the ordinary poll-backed epoll wait. A
non-null mask returns `-1` and `ENOSYS` until a kernel owner can atomically
install masks, manage pending delivery, and block on readiness.

## Evidence

`test/01_unit/os/libc/simpleos_epoll_pwait_honesty_test.c` passed under strict
C compilation with SimpleOS headers. It checks rejection of a non-null mask
and preserved ordinary empty-wait behavior for `NULL`.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

# SimpleOS epoll_pwait signal-mask false success

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

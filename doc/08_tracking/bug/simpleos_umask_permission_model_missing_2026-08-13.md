# SimpleOS `umask` needs end-to-end permission ownership
**Status:** OPEN (unverified 2026-09-12)

## Status

Open; no safe local repair applied.

## Evidence

`src/os/libc/simpleos_libc_ext.c` currently returns a fixed old mask from
`umask`, while `src/os/libc/simpleos_libc.c::open` discards the variadic create
mode on the guest syscall path and `src/os/libc/simpleos_fs.c::mkdir` forwards
an unmasked mode.  A local mask variable would still falsely imply it governed
new object permissions.

## Unblock condition

Define a kernel/VFS permission owner and pass effective `(requested & ~mask)`
mode through both open-create and mkdir atomically.  The owner must retain the
per-process mask, enforce/read back permissions, and provide regressions for
open-create and mkdir under changed masks.  Until then this API cannot support
permission-sensitive deployment claims.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

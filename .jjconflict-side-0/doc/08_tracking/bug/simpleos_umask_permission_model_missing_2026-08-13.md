# SimpleOS `umask` needs end-to-end permission ownership

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

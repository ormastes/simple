# SimpleOS credential identity requires a kernel owner

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

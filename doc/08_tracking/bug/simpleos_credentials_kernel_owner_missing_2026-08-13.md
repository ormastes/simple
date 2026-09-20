# SimpleOS credential identity requires a kernel owner
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


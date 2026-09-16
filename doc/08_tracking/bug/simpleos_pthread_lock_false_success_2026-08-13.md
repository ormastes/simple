# SimpleOS pthread lock false success

## Status

Mitigated: mutex and rwlock operations fail closed pending a synchronization
owner.

## Defect

The libc mutex and rwlock APIs returned success without changing state or
serializing access. Any target component that trusted a successful lock could
enter shared critical sections concurrently, causing ownership races and
memory corruption while the facade claimed POSIX synchronization.

## Current boundary

Non-null mutex/rwlock initialization, lock, try-lock, unlock, destroy, and
attribute operations return `ENOSYS`. Required null arguments return `EINVAL`.
Rejected initialization does not mutate caller storage. Condvar operations
remain consistently unsupported until a kernel-owned atomic lock-release and
wait/park transition exists.

## Evidence

`test/01_unit/os/libc/simpleos_pthread_sync_honesty_test.c` passed strict C
compilation with SimpleOS headers. It checks all mutex/rwlock operations,
null handling, and that failed initialization preserves sentinel storage.

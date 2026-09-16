# Server-data VFS fd binding remains blocked

The attempted `/srv/data/{web,db}` DBFS syscall binding was reverted after two
independent static-review cycles. Protected open therefore intentionally keeps
returning `ENOSYS`; it must not fall through to the legacy FAT32 side table.

## Proven prerequisites already present

- `ServerDataNamespaceOwnerV1` derives authority from the current TCB and a
  sealed DBFS-root mount identity.
- MountTable owns generational virtual file objects and positioned DBFS I/O.
- The new OFD and descriptor owners provide immutable access mode, shared
  offset sequencing, generational aliases, I/O pins, and close tickets.

## Exact blockers

1. A production adapter needs a non-cyclic, visibility-correct boundary among
   scheduler, namespace, VFS, fd-compat, and syscall packages. Importing the
   scheduler hub from an fd leaf creates a scheduler ↔ fd cycle; current
   `pub(package)` APIs cannot legally cross those package boundaries.
2. DBFS writes advance MountTable content generation and DBFS mutation epoch.
   A sealed mutation transaction must advance every exact-prestate active
   server lease, not just the writer, while retaining rejection for unrelated
   or externally changed state.
3. Numeric fd reservation, OFD creation, descriptor installation, VFS open,
   and canonical-path publication need one recoverable transaction. Mutating
   open flags (`O_CREAT`, `O_TRUNC`) cannot be enabled until later installation
   failure can restore the filesystem side effect exactly.
4. `dup`, `dup2`, `fcntl(F_DUPFD*)`, fork, and lseek currently operate only on
   the legacy fd table. Until joint fd-compat/OFD transactions exist, DBFS fds
   must be rejected before those paths mutate anything; otherwise aliases,
   offsets, and replacement close behavior diverge or leak.
5. Exit/exec must drain DBFS pins, close exact MountTable objects, destroy the
   fd-compat lifecycle context, restore the previously active legacy fd owner,
   and revoke namespace/launch authority even when backend cleanup fails.
   Unresolved close tickets need a bounded persistent quarantine/retry owner;
   they cannot disappear after descriptor-context destruction.
6. Acceptance coverage must model wrong task/lifecycle, stale generations,
   cross-task seal advancement, partial cursor commits, rollback, exact-once
   close, no-context exit, cleanup failure, and fail-closed alias/seek paths.

## Required next architecture slice

Introduce a scheduler-independent `ServerDataVfsCommandOwnerV1` with opaque
current-task command leases, a bounded pending-open/close transaction table,
and explicit friend facades for scheduler and syscall packages. Lifecycle code
must call the cleanup facade before generic fd teardown, but authority revocation
must be unconditional; failed backend cleanup moves to retained quarantine.

No tests, builds, SPipe, optimizer, benchmarks, or runtime verification were
run in this lane.

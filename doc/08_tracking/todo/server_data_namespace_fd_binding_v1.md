# TODO: bind protected DBFS objects to production descriptor owners

## Current blocker

The C ABI `open`/`rename` path is now task-bound and fail-closed for
`/srv/data/web` and `/srv/data/db`. MountTable can return a generational virtual
file object, and the OFD plus descriptor owners exist, but the production
syscall path still uses the legacy FAT32 fd registry and has no atomic
transaction spanning virtual-object open, OFD creation, descriptor alias
publication, and exact rollback/close.

## Required completion

- Derive `(task_id, lifecycle_generation)` only from the current TCB.
- Open through the canonical MountTable owner after Active namespace approval.
- Bind the virtual object to an OFD backend record and exact descriptor context.
- Roll back virtual object, OFD, fd number, and namespace operation pin in
  reverse order; quarantine every ambiguous close/publication outcome.
- Route read, write, sync, seek, truncate, dup/fork, exec, close, and task exit
  through the same alias/OFD owners before enabling successful protected open.
- Apply the same current-task operation pin to stat, mkdir, unlink, rmdir, and
  directory iteration before enabling any protected path operation.
- Revalidate the namespace lease and mount seal for every operation pin.
- Preserve the current `ENOSYS` boundary until the complete transaction exists.

No direct `DbdDbfsAdapter`, copied driver, raw MountTable handle, or
caller-supplied task identity is an acceptable shortcut.

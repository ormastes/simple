# SimpleOS `realpath` must not fabricate canonical paths

## Status

Fixed and focused C-tested on 2026-08-13.

## Fault

`src/os/libc/simpleos_libc_ext.c` previously copied a caller-provided spelling
into a buffer and returned it from `realpath`.  It neither resolved `.`/`..`,
symlinks, or existence, nor made relative paths absolute.  Treating that value
as canonical could authorize a path outside a containment boundary.

## Repair

The public shim now returns `NULL` with `errno=ENOSYS` for every request.  A
VFS-owned resolver must provide root/capability-bound canonical traversal,
loop bounds, and a no-follow/open-at style consumer boundary before this API
can be advertised as implemented.

## Evidence and resume

`test/01_unit/os/libc/simpleos_realpath_honesty_test.c` covers traversal,
relative, missing, oversized, and null paths. The strict hosted C harness
passes after providing the guest-private errno ABI, a stub syscall dependency,
and a `SIZE_MAX` compatibility guard in the guest headers.

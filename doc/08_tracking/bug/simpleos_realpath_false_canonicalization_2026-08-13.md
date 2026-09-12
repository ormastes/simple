# SimpleOS `realpath` must not fabricate canonical paths
**Status:** OPEN (unverified 2026-09-12)

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

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

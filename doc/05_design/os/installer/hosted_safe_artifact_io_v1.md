# Hosted safe artifact I/O v1

Status: BLOCKED AT HOST CAPABILITY BOUNDARY

## Purpose

This contract is the minimum hosted-file boundary required by the Simplebox
manifest signer.  The signer remains pure Simple and must receive bytes and a
publication receipt from one typed owner; it must not combine path predicates
with later path opens.

## Read owner

One mutable owner must perform the following owner-controlled lifecycle.  It is
not an atomic snapshot of a concurrently writable inode:

1. Begin from a pre-opened trusted root authority.  Resolve a relative path
   beneath it with no `..`, absolute escape, symlink, or magic-link traversal
   (equivalent to `RESOLVE_BENEATH|RESOLVE_NO_SYMLINKS|RESOLVE_NO_MAGICLINKS`),
   and apply the caller's mount-crossing policy.  Enforce bounded path and
   component lengths.  Open with close-on-exec.
2. Obtain regular-file type, device, inode, and nonnegative size from that same
   open descriptor.
3. Reject a size above the caller's positive bound before allocation.
4. Read exactly the snapshotted size through that descriptor using a bounded
   loop which handles interruption and short reads.  Growth is ignored;
   premature EOF is failure.
5. Re-stat the descriptor and reject changes to device, inode, size, file type,
   ctime, or mtime before returning an independently owned byte array.  This is
   mutation detection, not proof against same-inode concurrent writes which
   restore metadata.  Signer inputs therefore require an immutable or
   owner-locked input authority, or a provider snapshot primitive.  The signer
   signs the exact returned bytes and makes no claim about later path contents.
6. Close exactly once on every success and failure path.  A close failure makes
   the whole operation fail.

The descriptor is an owned move into this lifecycle.  It is never returned,
copied, stored globally, or accepted from the caller.

## Publication owner

One mutable owner must:

1. Resolve a same-filesystem destination directory beneath a pre-opened trusted
   root using the containment rules above.
2. Prefer an unnamed owner-only `O_TMPFILE` inode and publish that exact fd with
   `linkat(AT_EMPTY_PATH)` using absent-destination semantics.  Where that is
   unsupported, use a retained, owner-private staging directory which is not
   writable by an attacker, validate its ownership/mode, and create-exclusive
   there.  Named staging in an attacker-writable directory is forbidden.
   A named leaf uses at least 128 bits from the canonical OS CSPRNG, retries a
   bounded number of collisions, and fails closed if entropy is unavailable.
3. Write the complete bounded payload through the retained descriptor, handle
   short writes and interruption, fsync it, and confirm its regular-file
   identity with fstat.
4. Atomically publish to an absent destination using fd-identity linking or
   kernel rename-no-replace semantics on the same filesystem.  A destination
   race must return `already-exists`, never replace it.
5. Fsync the destination directory after publication.  Before publication an
   unnamed inode is closed; a named inode may be unlinked only inside the
   owner-private staging directory.  If identity cannot be proved, safely leak
   or quarantine it instead of deleting a path which may name a replacement.
   A failure after namespace publication is reported as
   `published-not-durable`; it must not delete the published destination.

The informational result contains outcome and byte count.  Authority-bearing
success uses a package-private constructor plus an owner-held positive,
nonwrapping generation/seal which is checked and consumed on redemption;
copying the value cannot duplicate authority.

All size conversions reject overflow.  Empty inputs and outputs are valid when
the caller's role permits them.  Read/write loops have an explicit positive
progress invariant and byte ceiling.  Interrupted open/read/write/stat/fsync/
publish/cleanup/close operations are retried only where the platform documents
that retry as safe and within a bounded interruption budget.  Cleanup failure
is retained alongside the primary error.  `already-exists`, `unsupported`,
`cleanup-failed`, and `published-not-durable` are distinct results.  A close
failure after publication never implies rollback.

## Current facade mismatch

The canonical `std.io.FileHandle` supplies descriptor-bound reads, metadata,
flush, and close only *after* `rt_io_file_open`, whose modes do not express
no-follow or create-exclusive.  `file_is_regular_no_follow` is a separate path
predicate and cannot bind a subsequent open.  `rt_file_create_excl` does not
retain a typed descriptor and its native provider does not request no-follow.
`file_rename` replaces an existing destination on POSIX and has no
rename-no-replace mode.  Consequently these operations cannot be safely
composed in pure Simple.

No executable owner is added until the canonical host facade exposes the
missing atomic primitives consistently in interpreter and native providers.
This is fail-closed: the signer must continue to report safe I/O unavailable.

## Static acceptance contract

- No check-then-open or check-then-rename sequence may authorize success.
- Every returned byte is read from the descriptor whose identity was checked.
- Every staged byte is written through the exclusively created descriptor,
  and named staging lives only in a validated owner-private directory.
- Existing destinations are never replaced.
- All buffers and loops are bounded by an explicit caller limit.
- Descriptor and staging cleanup have one authoritative mutable owner.
- Authority receipts require owner-side generation/seal redemption; their
  value representation alone never proves success.
- Interpreter and native implementations must have identical failure classes
  before this capability is exported to the signer.

No tests, builds, SPipe, benchmarks, optimizer, or runtime verification were
run for this static contract.

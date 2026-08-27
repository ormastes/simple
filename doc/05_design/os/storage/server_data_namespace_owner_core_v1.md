# Server-data namespace owner core V1

## Scope

This phase adds the bounded authority capsule between the scheduler's sealed
`/SERVERS.ELF` launch grant and the canonical DBFS-root MountTable seal. It does
not wire syscalls, DBD, HTTP persistence, raw drivers, or block I/O.

## Ownership and transaction

The VFS boot-state module remains the sole MountTable owner and exposes three
narrow opaque-seal operations. The namespace owner lives in the scheduler
package, so redemption tickets and state transitions retain package scope
rather than becoming global APIs. `ServerDataNamespaceOwnerV1` owns one checked mutex,
the live opaque seal, and at most 64 generational lease rows. Boundary values
are opaque handles; paths are bounded copies. No driver or MountTable escapes.
The boot-state module serializes every value-copy/commit MountTable owner API
and every root-seal operation with one checked mutex. Unlock ambiguity
quarantines all later canonical-table mutations and revalidations.

Acquisition follows `scheduler -> mount revalidation -> namespace prepare ->
scheduler commit -> mount revalidation -> namespace activate`. No two ranked
locks are held together. A preparation failure rolls the exact scheduler
ticket back. An ambiguous commit, unlock, revalidation, or publication retains
a non-reusable quarantine tombstone and quarantines the scheduler ticket.

Revocation removes the exact `(task_id, lifecycle_generation)` namespace row
before calling scheduler grant teardown. A namespace ambiguity prevents grant
teardown rather than risking live namespace authority without its owner row.

## Fixed policy

Only canonical paths at or below `/srv/data/web` and `/srv/data/db` are
admitted. Web permits read, write, create, remove, rename within its own root,
and sync. Database permits those operations plus atomic replacement. Rename
cannot cross roots. Empty, relative, over-4096-byte, duplicate-separator, dot,
and parent-traversal paths fail closed.

## Complexity and allocation

Every owner lookup scans at most 64 rows, so time is O(64) and storage is
O(64). Mount seal revalidation remains outside the owner mutex. Authorization
canonicalizes/checks a bounded path once and retains no path or payload copy.
Future syscall wiring must add operation pins before any I/O and must not make
these package-private handles public until production entropy backs both nonce
words.

The focused spec covers exact task/lifecycle and mount-fact matching, terminal
generation handling, the two revalidation ordering points, rollback and
quarantine presence, namespace-before-grant revocation order, and exact path
policy. These specs are authored but intentionally not executed in this wave.

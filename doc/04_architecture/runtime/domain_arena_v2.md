<!-- codex-architecture -->
# DomainArena V2 compatibility architecture

DomainArena V2 is an additive owner-result lane. DomainArena V1 remains the
canonical allocation producer and retains its V1 evidence schema and hash.
V2 is not live evidence and cannot promote or relabel a V1 receipt.

## Ownership contract

The arena owner is the execution domain that creates the arena, mints
`DomainArenaOwnerCapabilityV2`, and commits or rolls back generations. Child
writers receive only an opaque minted span. Bytes and span-bank entries are
staged in the inactive fixed bank; committed readers resolve the active bank
through the private authority state. No child or reader receives a raw address.

Publication mutates one private `DomainArenaAuthorityV2` state object containing
the committed snapshot, bank selector, and owner nonce. Commit validates the
owner capability and checkpoint before replacing the committed snapshot and
flipping the selector. Rollback clears the inactive bank and restores the
previous committed snapshot.

The current Simple implementation uses an explicit single-owner, non-Send type boundary:
all arena methods, including reads, are owner-thread confined and no arena
value may cross a task/process boundary. A future concurrent adapter must wrap
the authority with a serialized owner queue or seqlock before permitting shared
readers; V2 does not claim concurrent access.

The owner token is an internal constructor-minted value (the underscore-prefixed
mint helper is not part of the exported module surface), and checkpoints carry
only the authority binding, never the token itself. Foreign-domain handles are
rejected by the owner and nonce checks.

## Capacity and lifecycle

`try_create` validates arena identity, sealed profile, masks, alignment, quota,
and reference capacity before constructing either bank. The quota and reference
limits are fixed constants; rejected profiles return a typed construction error
without an invalid arena value. Once created, each bank is allocated exactly
once. Allocation only performs scalar checks and fixed-array writes. It does not
hash, stringify, concatenate, grow, or copy on the hot path.

Staging refs are writable only while their generation is open. Reads require an
exact `(arena, domain, generation, offset, size, mint)` tuple present in the
committed ref bank, so forged subspans and unpublished bytes are rejected.

## Evidence boundary

V2 cold-path evidence uses schema 2 and hashes committed bytes, while V1 hash
functions and producer artifacts remain unchanged. A V2 snapshot row is
compatibility evidence only; release admission continues to consume the
existing V1 allocation and fault-injection lanes until an explicit migration.

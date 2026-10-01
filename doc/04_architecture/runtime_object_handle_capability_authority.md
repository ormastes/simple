# Runtime Object-Handle Capability Authority

## Decision

Cross-domain object handles are authorized by one bounded, runtime-owned table,
not by the handle's value fields. The C native runtime and Rust bootstrap
runtime expose the same scalar ABI:

- `rt_object_handle_owner_create()`
- `rt_object_handle_owner_destroy(owner_handle)`
- `rt_object_handle_capability_mint(owner_handle, target, generation, region)`
- `rt_object_handle_capability_consume(token, owner_handle, target, generation, region)`
- `rt_object_handle_capability_revoke(token, owner_handle)`

Zero is always failure and is never a valid token. Owner handles and capability
tokens are independent positive 63-bit bearer values from operating-system
secure entropy; entropy failure or repeated collision fails closed. Neither
value reveals the table slot or its internal generation. The fixed capacity is
64 capabilities and 64 owner handles.

## Ownership and concurrency

Each live entry binds a runtime-issued owner handle, exact target domain, object generation,
and region identifier. Consume checks the complete tuple and atomically clears
the entry. Revoke checks the token generation and minting owner, then clears
the entry. Both operations serialize through the authority mutex, so concurrent
consume-versus-revoke has exactly one winner. No ABI value is a pointer.
Owner destruction takes the same lock, revokes all capabilities belonging to
that owner, and retires its handle before releasing the slot. Later reuse is
reseeded from secure entropy; the stale bearer cannot acquire the new owner's
authority. Concurrent destroy and consume are ordered by the lock.

The Simple `RuntimeObjectHandleCapabilityAuthorityV1` is the actor scheduler's
production facade. `ObjectHandleCapabilityRegistryV1` remains a deterministic
interpreter test model; it is not a security authority and production actor
code does not use it.

Actor scheduler `stop()` destroys its owner once; a repeated stop is inert.
Restarting creates a fresh owner bearer. Bearer secrecy remains an operational
requirement: possession of either opaque value conveys its represented right.

## Evidence

The canonical gate `scripts/check/check-object-handle-capability-authority.shs`
exercises C decision vectors, tuple rejection, replay, capacity, revocation,
slot reuse, stale tokens, and the consume/revoke race. Focused Rust tests cover
the same decisions without comparing random token values. The Simple unit spec
covers reference-model boundary behavior separately.

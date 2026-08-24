# NVFS Device Identity Owner V1

## Scope

This prerequisite owns only the canonical identity relationship between one
outer `NvfsPosixDriver`, one inner device-backed `DbFsDriver`, and one admitted
device region. It does not close, unregister, mount, unmount, or dispatch I/O.

## Ownership and lifecycle

The process-global mutex-protected owner is the only mutable authority. Public
reservations and bindings are copied opaque handles. Admission reserves a
monotonic outer identity, generation, nonce, and exact
`(device_owner_id, base_block, block_count)` before device registration. After
registration, activation binds the positive inner DBFS instance identity.

The lifecycle is `Free -> Reserved -> Active -> Terminal -> Free`. Failed
pre-registration admission rolls `Reserved -> Free` while advancing its
generation, so repeated constructor failures cannot consume terminal capacity.
Indeterminate cleanup moves `Active -> Quarantined`. Terminal eviction advances
the slot generation before reuse; a generation-max slot is permanently quarantined.
Nonce or outer-identity exhaustion quarantines the complete owner rather than
wrapping.

Admission rejects overlapping live regions belonging to the same stable device
owner. Half-open interval comparison permits adjacent regions, and distinct
device-owner identities remain independent.

## Complexity and bounds

Active validation, terminal transition, eviction, and stale rejection use the
opaque slot index and are O(1), with no allocation or identity copying on the
hot path. Reservation and activation may scan the fixed 256-slot table to find
a free slot and reject duplicate active region/inner identities. Terminal and
quarantine storage is bounded by that same capacity.

## Deferred integration

A future constructor must reserve first, register DBFS second, then activate.
Future teardown must refuse busy drivers, unregister DBFS, mark the binding
terminal only after confirmed cleanup, and explicitly evict its receipt. That
ordering is not claimed by this module.

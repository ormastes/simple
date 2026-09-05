# NVFS Device Identity Owner V1

## Scope

This owner binds the canonical identity relationship between one
outer `NvfsPosixDriver`, one inner device-backed `DbFsDriver`, and one admitted
device region and now serializes normal teardown.

## Ownership and lifecycle

The process-global mutex-protected owner is the only mutable authority. Public
reservations and bindings are copied opaque handles. Admission reserves a
monotonic outer identity, generation, nonce, and exact
`(device_owner_id, base_block, block_count)` before device registration. After
registration, activation binds the positive inner DBFS instance identity.
If DBFS reports an error after its transaction owner becomes quarantined, the
reservation is quarantined rather than rolled back because registration may
already have committed. DBFS instance allocation fails before signed overflow;
identifiers never wrap or reuse.

The lifecycle is `Free -> Reserved -> Active -> Closing -> Terminal -> Free`.
Busy cleanup returns `Closing -> Active`; a determinate retryable failure moves
`Closing -> Retryable -> Closing`. Failed
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

## Teardown integration

`NvfsPosixDriver.new_on_owned_device` reserves before DBFS registration and
activates only after registration succeeds. Every owned-driver operation
performs the O(1) binding validation, so a copied driver becomes stale while
cleanup is closing/retryable and remains stale after terminal completion.

DBFS performs its open-file and directory-handle busy scan, exact device
unregister, inode/fd reclamation, and bounded 256-entry replay receipt under
its canonical transaction lock. The identity owner enters Terminal only after
DBFS confirms the release (including a recognized replay after an ambiguous
unlock). Unknown cleanup state is quarantined. Terminal eviction advances the
identity generation; evicted DBFS receipts cannot target a replacement because
DBFS instance identifiers are monotonic and never caller-selected.

Connector wiring remains deferred until the connector has one serialized
operation-lease owner. Session validation followed by a copied-driver call is
not a fence: close must first reject new leases, drain existing leases, prove
the driver is not busy, then close the session and unmount. The unsafe draft
which lacked that owner was reverted.

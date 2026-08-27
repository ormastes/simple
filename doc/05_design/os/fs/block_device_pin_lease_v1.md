# Block-device pin lease v1

## Purpose

`block_device_identity_owner_v1` is the sole mutable authority for registered
block-device identities and their filesystem-visible regions.  Only the holder
of the existing private-nonce `BlockDeviceRegistrationV1` lifecycle authority
may acquire an opaque pin after validating the exact backend kind, owner,
backend generation, base LBA, and sector count.  The pin closes the interval
between device validation and mount teardown: replacement and unmount return
`Busy` until every pin has reached a known released state.

## Ownership and bounds

- The module-global mutex owns 64 device slots and at most 128 pin slots.
- `BlockDeviceSealV1` remains an observational handle.
- `BlockDeviceRegistrationV1` remains the only replace/unmount and pin-issue
  authority. An observational seal cannot create lifecycle-blocking work.
- `BlockDevicePinLeaseV1` is an opaque scoped lease.  It exposes only
  observational device slot/generation values and carries no device lifecycle
  authority.
- A private monotonically increasing nonce binds each lease to its exact pin
  slot and registered identity generation.  Successful release retires the
  slot generation, so copied lease values become stale.

Pin acquisition and device pin-count publication occur in one owner-locked
transition. Acquisition scans at most 128 slots; validation and release use
direct slot lookup. The arrays grow only toward their fixed capacities. Simple
value/COW lowering may copy bounded owner state during a locked transition, so
this source-only lane does not claim allocation-free execution.

## Indeterminate release

A provider that cannot prove whether its external release completed calls
`block_device_identity_quarantine_unpin_v1`.  That transition does not decrement
the canonical pin count.  The device therefore remains busy and cannot be
replaced or unmounted.  The provider retains the same opaque lease as retry
authority and calls `block_device_identity_retry_unpin_v1` only after it can
prove release.  The first successful retry consumes the owner record; all
copied leases then fail stale.  A normal unpin cannot silently clear a
quarantined record.

Counter exhaustion fails closed by quarantining the owner rather than wrapping.
Pin-slot generation exhaustion retires the individual slot permanently.

## FAT32 integration boundary

The future FAT32 publication transaction must acquire the pin before reading
the BPB or recovery state.  Rejection rolls the pin back.  Successful commit
moves the opaque lease into the canonical mount owner, which retains it until
operation admission is stopped, in-flight operations drain, the filesystem is
flushed, and provider release is known.  This module does not publish mounts,
retain a `BlockDevice`, or allow fixture constructors to mint a pin.

## Acceptance contract

1. Only current registration authority can issue a pin, and the pin binds the
   exact registered device generation and complete region.
2. A live or quarantined pin makes replace and unmount return `Busy` without
   changing canonical identity state.
3. Normal unpin and successful retry consume exactly one owner record and make
   copied leases stale.
4. Indeterminate unpin keeps the pin counted until an exact retry succeeds.
5. Capacity and nonce exhaustion fail closed without unbounded storage.

This source/spec contract is unverified in the current no-verification lane.

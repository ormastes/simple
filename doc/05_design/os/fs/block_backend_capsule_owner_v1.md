# Block backend capsule owner v1

## Purpose

FAT32 must not pair an authenticated device pin with an unrelated caller-owned
`BlockDevice`. This owner binds the concrete dispatch object to the exact
controller identity, generation, and LBA region before any filesystem I/O.

## Ownership and layout

- The block-device identity owner remains canonical for device identity and
  pin lifetime.
- The capsule registry preallocates 32 heap-resident slot owners at module
  initialization. The registry never grows or relocates those slot owners.
- Each slot owns its backend, exact region, generation, private nonces, and at
  most 64 operation reservations under a slot-local mutex.
- A public seal and I/O lease are opaque handles. Value copies carry no mutable
  authority: the canonical slot record determines whether they remain usable.
- Registration is package-private and requires current lifecycle authority from
  the identity owner. Ordinary `BlockDevice` implementations cannot construct
  a seal or install themselves through the public I/O surface.
- Registration retains the identity owner's exclusive backend pin for the full
  capsule lifetime. A copied device registration therefore cannot bind a
  second backend object to the same identity.

## Dispatch and locking

The registry lock only resolves or installs a stable slot reference. Identity
pin acquisition happens without it. Read, write, flush, release fencing, and
teardown use only the selected slot mutex. No backend method is invoked while
the registry or block-device identity mutex is held. Thus unrelated devices do
not share backend dispatch serialization.

Relative LBAs are checked against the authenticated half-open region before the
base LBA is added. The identity registration, identity pin, capsule binding,
and stored controller identity must all name the same slot and generation.

## Release and teardown

Release changes the operation reservation from `Active` to `Releasing` under
the slot mutex. That waits for any in-flight dispatch and rejects all later
dispatch from copied handles. It then consumes the device pin. An indeterminate
provider release changes both owners to quarantine; only exact retry may finish
the reservation. Capsule teardown rejects live or quarantined reservations,
flushes under the slot owner, releases the exclusive backend pin, and either
retires the generation or retains the backend and close authority in quarantine
after an uncertain durability boundary. Exact-registration retry distinguishes
flush retry from identity-unpin retry and does not allocate another slot.

## Bounds and performance

Registration scans at most 32 capsule slots and acquisition scans at most 64
reservation slots. Dispatch is O(1) after one bounded registry lookup. The hot
path holds no global identity lock and makes one result-buffer copy imposed by
the current `mutex_with_lock` value-state API. No unbounded replay, quarantine,
or backend collection is introduced.

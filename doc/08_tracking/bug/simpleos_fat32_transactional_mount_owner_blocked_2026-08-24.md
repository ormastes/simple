# FAT32 transactional mount owner is blocked on device and operation ownership

- Status: OPEN / two unsafe drafts reverted
- Scope: production kernel FAT32 mount publication and teardown
- Date: 2026-08-24

## Required outcome

One non-copyable owner-side transaction must publish the canonical filesystem
object, backing-device identity, mount generation/seal, recovered atomic-replace
capability, and already-mounted state. Rejection must publish nothing. The same
owner must fence operations and retain the only consume-once close authority.
Test-only filesystem constructors must never mint a live production seal.

## Concrete blockers

1. `std.fs_driver.block_device.BlockDevice` exposes sector I/O and flush but no
   authenticated controller/namespace/device identity. A BPB volume serial is
   forgeable filesystem metadata and cannot substitute for device identity.
2. Existing syscall and FAT32 descriptor paths read `fat32_mount_ready`,
   `fat32_mount_fs`, and `fat32_mount_dev` separately and retain ordinary
   reference aliases. A close transaction can therefore race between the
   readiness check and unwrap/use. There is no bounded operation-lease/inflight
   fence through which close can quiesce users before flushing and clearing.
3. `Fat32Filesystem` fields and test constructors are caller-visible mutable
   state. A boolean claiming that `mount()` ran is forgeable. Production commit
   needs a module-private opaque receipt produced only after the device-backed
   BPB, recovery, and bounded root read succeed.
4. Mutex unlock failure after publication currently has no ownership-preserving
   result shape. Returning an ordinary error after canonical state changes can
   strand the mount while the caller drops its only close session.
5. Atomic-replace capability is separately mutable global state and direct
   mutation adapters do not consume a mount-bound operation lease.
6. The block-device identity owner now implements a bounded,
   generation-and-region-bound pin lease issued only from current registration
   authority. Live and indeterminate-release pins
   make replace/unmount return `Busy`; successful release consumes the private
   owner record and invalidates copied leases. The remaining blocker is moving
   that opaque lease through the production `BlockDevice` adapter into the
   canonical FAT32 mount owner; no existing FAT32 publication path owns it yet.

## Rejected draft

A draft added a mutexed ready-last commit and a reference-semantic close session.
Independent static review rejected it because readers did not acquire the same
lock, close flushed with operations potentially in flight, device identity was
incorrectly derived from BPB volume serial, mutable fields could forge mount
evidence, and post-commit unlock failure could report failure after publication.
The draft and its inadequate negative-only spec were reverted.

A second draft attempted a bounded two-phase metadata publication owner using
the committed `BlockDeviceSealV1`. Static ownership review rejected it before
commit because revalidating the seal at prepare or commit cannot close the
cross-owner interval: device lifecycle authority remains independently
callable. The draft was removed; no API now claims transactional FAT32 mount
publication from an unpinned observational seal.

## Safe implementation order

1. Extend the storage handoff with an owner-issued opaque namespace identity and
   bind every production `BlockDevice` adapter to it.
2. Move the implemented bounded device pin lease into the mount transaction
   before probing. Rollback releases it; committed mount state owns it until
   quiescent close. Do not reconstruct a lease from observational identity.
3. Add a private successful-mount receipt that cannot be constructed by fixture
   constructors or field mutation.
4. Route every mounted FAT32 operation through one bounded generational lease
   owner; close first stops admission, then drains inflight leases, flushes, and
   invalidates the generation without holding a lock across reentrant I/O.
5. Make commit/close receipts represent committed-unknown outcomes without
   losing recovery/close authority.
6. Only then replace legacy publication and add lifecycle/race acceptance for
   duplicate mount, rollback, copied session aliases, stale generations,
   capability gating, flush failure, and successful remount.

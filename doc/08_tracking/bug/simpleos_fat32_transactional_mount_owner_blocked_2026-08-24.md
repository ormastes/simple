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
6. `block_device_identity_owner_v1` now authenticates an exact device region,
   but its seal is explicitly observational. Validation and FAT32 publication
   are separate owner transactions. The registration holder can replace or
   unmount the device after validation and before (or after) mount commit, so a
   mount owner built only from the existing seal has a TOCTOU stale-device
   race. The block-device owner needs a bounded, generation-bound mount pin:
   `block_device_identity_pin_v1(seal)` must increment canonical pin state and
   return an opaque consume-once pin lease; replace/unmount must return `Busy`
   while pins exist; `block_device_identity_unpin_v1(lease)` must invalidate
   copied leases and release exactly once. Pin capacity and nonce exhaustion
   must fail closed and quarantine rather than wrap.

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
2. Add the bounded device pin/lease transition described above and require the
   mount transaction to acquire the pin before probing. Rollback releases it;
   committed mount state owns it until quiescent close.
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

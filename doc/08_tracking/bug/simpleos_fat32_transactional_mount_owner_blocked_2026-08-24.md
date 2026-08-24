# FAT32 transactional mount owner is blocked on device and operation ownership

- Status: OPEN / unsafe draft reverted
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

## Rejected draft

A draft added a mutexed ready-last commit and a reference-semantic close session.
Independent static review rejected it because readers did not acquire the same
lock, close flushed with operations potentially in flight, device identity was
incorrectly derived from BPB volume serial, mutable fields could forge mount
evidence, and post-commit unlock failure could report failure after publication.
The draft and its inadequate negative-only spec were reverted.

## Safe implementation order

1. Extend the storage handoff with an owner-issued opaque namespace identity and
   bind every production `BlockDevice` adapter to it.
2. Add a private successful-mount receipt that cannot be constructed by fixture
   constructors or field mutation.
3. Route every mounted FAT32 operation through one bounded generational lease
   owner; close first stops admission, then drains inflight leases, flushes, and
   invalidates the generation without holding a lock across reentrant I/O.
4. Make commit/close receipts represent committed-unknown outcomes without
   losing recovery/close authority.
5. Only then replace legacy publication and add lifecycle/race acceptance for
   duplicate mount, rollback, copied session aliases, stale generations,
   capability gating, flush failure, and successful remount.


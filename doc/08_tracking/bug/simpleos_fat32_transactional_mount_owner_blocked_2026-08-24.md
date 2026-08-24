# FAT32 transactional mount owner is blocked on device and operation ownership

- Status: OPEN / three unsafe drafts reverted
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

A third draft acquired the committed pin before calling `Fat32Filesystem.mount`
and added bounded generational operation leases plus drain/flush/detach/unpin
ordering. Static ownership review rejected it before commit for two earlier
boundary defects that the mount owner cannot repair locally:

1. The caller-supplied `BlockDevice` trait object has no owner-issued identity
   binding. A caller could pin registered device A while supplying device B for
   BPB/root reads and flush, producing a mount seal that falsely names A.
2. `Fat32Filesystem.mount` calls `fat32_atomic_replace_publish_caps` during
   recovery, before its later root-cluster reads and before canonical mount
   commit. A failed root read or commit can therefore publish capability state
   even though the mount transaction rejects.

That draft and its inadequate tautological spec were removed. The bounded
operation-slot and close-ordering design was locally sound, but cannot be
published until both identity binding and side-effect-free probing exist.

A fourth draft retained a generic `BlockDevice` behind a package-private
pin-bound I/O handle and attempted to compare identity methods exposed by the
trait. Two independent static-review cycles rejected it and it was reverted:

1. Identity methods implemented by the same caller-supplied trait object are
   self-attestation, not controller/namespace-owner authentication. A backend B
   can report A's metadata, so comparison cannot authorize the object.
2. Calling identity or I/O trait methods under the global identity mutex permits
   reentrant deadlock and serializes unrelated devices.
3. Moving dispatch outside that mutex through a module-global dynamic backend
   array makes different-slot access race with array mutation/reallocation.
   An `io_busy` bit protects lifecycle metadata, not the shared vector storage.

The safe next boundary is a bounded, fixed-location backend capsule created by
the concrete controller/namespace owner. It must carry an opaque owner-issued
seal that ordinary `BlockDevice` implementations cannot construct. The identity
owner may then validate that seal, reserve one slot, invoke the per-slot capsule
without the global identity lock, and consume the capsule handle with the pin.
Until that provider-owned capsule exists, a package-private facade alone does
not make caller-supplied block I/O authenticated.

## Safe implementation order

1. Extend the storage handoff with an owner-issued opaque namespace identity and
   bind every production `BlockDevice` adapter to it.
2. Add an owner-issued authenticated block-device I/O handle whose private
   identity is the same identity retained by `BlockDevicePinLeaseV1`; a bare
   caller-supplied `BlockDevice` plus a separate pin is insufficient.
3. Split FAT32 probing/recovery into a side-effect-free candidate operation.
   It must return capability material without calling
   `fat32_atomic_replace_publish_caps`; publish that material only in the same
   canonical commit as filesystem/device/pin state.
4. Move the bounded device pin lease and authenticated I/O handle into the mount
   transaction before any device method. Rollback releases or quarantines the
   pin; committed state retains it through quiescent teardown.
5. Add a private successful-mount receipt that cannot be constructed by fixture
   constructors or field mutation.
6. Route every mounted FAT32 operation through one bounded generational lease
   owner; close first stops admission, then drains inflight leases, flushes, and
   invalidates the generation without holding a lock across reentrant I/O.
7. Make commit/close receipts represent committed-unknown outcomes without
   losing recovery/close authority.
8. Only then replace legacy publication and add lifecycle/race acceptance for
   duplicate mount, rollback, copied session aliases, stale generations,
   capability gating, flush failure, and successful remount.

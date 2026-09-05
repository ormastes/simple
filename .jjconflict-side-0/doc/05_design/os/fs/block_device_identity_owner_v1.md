# Block-device identity owner v1

## Scope

This contract supplies authenticated, bounded device-region identity needed by
transactional FAT32 mount work. It does not publish a mount, retain a
`BlockDevice`, perform I/O, or claim that FAT32 is transactionally mounted.

## Ownership

The module-global mutex owner is the only canonical mutable state. A concrete
block-device backend keeps its I/O object and supplies a stable backend kind,
owner ID, backend generation, and sector region. `BlockDeviceSealV1` is a
copyable observational handle. `BlockDeviceRegistrationV1` carries the
lifecycle nonce, but lifecycle authority is canonical and single-use: the
first successful replacement or unmount advances the slot generation, making
every copied registration stale.

## Invariants

- Backend kind, owner ID, generation, base LBA, and sector count are all
  nonzero/valid and bind exactly.
- Active regions on the same backend generation may not overlap. A backend
  owner may have only one live generation, forcing generation change through
  the authenticated replacement transition.
- Creation issues unique monotonic identity and
  lifecycle nonces; exhaustion quarantines instead of wrapping.
- Replacement is atomic: either the prior binding stays active or a new seal
  is issued after generation advance.
- Unmount invalidates observation and lifecycle authority before the slot can
  be reused.
- Storage is bounded to 64 slots. Generation exhaustion quarantines that slot.
- Validation is one indexed slot lookup. Create is bounded O(capacity) for
  overlap detection; replacement has the same bounded scan. No hot-path heap
  copy or dynamic dispatch is introduced.

## Integration boundary

A future FAT32 mount transaction must receive the exact binding from the
canonical device backend owner, create a registration before filesystem
probing, retain the registration in the mount owner, and publish only the
observational seal. Failed mount preparation must unmount the registration.
Device replacement must use `block_device_identity_replace_v1`; constructing a
new unrelated registration cannot preserve mount identity.

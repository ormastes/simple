# NVFS Connector Session Wiring Blocked by Device-Owner Teardown

## Status

Blocked prerequisite, found during static review on 2026-08-24. No runtime
verification was run. The rejected connector draft was reverted.

## Intended integration

The canonical connector lifecycle must:

1. construct the NVFS driver on the lease-windowed `BlockDevice` supplied with
   the canonical `NvmeSharedFilesystemInterface`;
2. mount the driver before opening `NvfsMountSessionV1`;
3. validate that exact session before each connector operation;
4. close the session before driver unmount;
5. reject stale copies, release exactly once, and keep all failure storage
   bounded without adding a parallel generic-VFS backend.

## Exact blocker

`NvfsHostedDriver.new_on_device` aliases
`NvfsPosixDriver.new_on_device`, which calls `DbFsDriver.open_on_device` and
registers device-backed DBFS/global inode state. However,
`NvfsPosixDriver.unmount()` currently returns `Ok(())` without invoking an
owned DBFS close/unregister operation. The DBFS unregister path is used for
constructor replay failure, not normal mounted-driver teardown.

Consequently, dropping the connector record after a nominally successful
unmount leaks the underlying device registration. Repeated connect/disconnect
cycles can grow owner state without bound. A connector-local quarantine cannot
fix this because it neither owns nor releases the deeper DBFS registration.

## Required prerequisite

Add a Pure Simple, idempotent, exactly-once device-backed close path owned by
`DbFsDriver`/`NvfsPosixDriver`. It must reject stale copies, refuse close while
open handles or outstanding operations exist, unregister the exact device and
inode/cache state, preserve the primary error on cleanup failure, and expose a
bounded recovery/quarantine policy. After independent review of that owner
path, wire the connector session in the ordering above and add lifecycle specs
covering normal release, repeated close, stale/recycled sessions, admission
rollback, unmount rollback, and registration-count return to baseline.

## Trust seam

The current `BlockDevice` trait exposes sector size but not stable device
identity or sector count. As in the existing NVMe filesystem mount factory, a
caller-provided device can only be trusted to represent the lease window; the
connector cannot prove that association until the block-device owner exports a
falsifiable lease-binding identity.

## Rejected teardown design review (2026-08-24)

A three-cycle independent static review rejected and caused reversion of an
unverified teardown draft. The remaining prerequisite is more specific:

- the bounded owner must canonically bind the outer `NvfsPosixDriver` identity
  to the inner DBFS instance, close nonce, and admitted device region; trusting
  the mutable outer `inst_id` lets one copied driver delete another instance's
  cache/tracking state while closing its own inner device;
- terminal replay may be bounded, but receipt eviction must make old copies
  stale without permitting another unregister or state resurrection;
- active validation cannot linearly scan up to 65,536 mounts on every file I/O;
  use a bounded O(1) slot+generation owner (or equivalent indexed owner) and
  keep validation under the same serialization domain as teardown;
- constructor nonce/identity admission must precede device registration, and
  indeterminate unlock remains explicit bounded fail-stop quarantine rather
  than being described as successful rollback;
- lifecycle evidence must include outer-id mutation, post-close copied-driver
  operations, cache isolation/reclamation, directory handles, busy retry,
  cleanup failure, terminal eviction, and registration count restoration.

No implementation from the rejected draft remains and no verification was
run.

## Identity-owner prerequisite progress (2026-08-24)

The bounded Pure Simple identity owner now exists at
`std.fs_driver.nvfs_device_identity_owner_v1`. It reserves the canonical outer
identity and admitted device region before registration, activates only with an
exact positive inner DBFS identity, validates copied bindings through one
slot+generation+nonce lookup, and provides bounded terminal eviction and
fail-stop quarantine. Static lifecycle specifications cover outer/inner/device
substitution, stale copied bindings after reuse, pre-registration rollback,
terminal replay, and indeterminate cleanup.

## Teardown and connector progress (unverified)

An owned constructor and teardown path now consume the identity owner. DBFS
performs a serialized busy check, exact unregister, cache reclamation, and
bounded replay retention; copied/mutated outer identities cannot redirect the
inner cleanup. The NVFS driver validates the binding on operations, provides a
directory-descriptor release path, and exposes busy/retryable/terminal close
transitions with terminal eviction.

The earlier connector wiring remained blocked and its unsafe draft was reverted
after independent static review. That review established the operation-fence
and preflight requirements implemented in the progress section below.

This work has only static specifications and remains unverified by explicit
instruction. The stable block-device identity trust seam also remains: the new
device connector requires a nonzero owner-issued identity because the generic
`BlockDevice` trait still cannot derive one itself.

## Operation-fence progress (unverified)

The bounded `nvfs_operation_lease_owner_v1` now aligns its O(1) slot lookup
with the authenticated device-identity binding. It permits one copied-driver
operation at a time, consumes exact operation nonces, enters Draining before
close observes an in-flight operation, rejects new work during drain/close,
and represents busy, retryable, terminal, and indeterminate-quarantine
transitions explicitly. `NvfsPosixDriver` registers only after identity
activation and fences every device-backed operation through that owner.

The narrow preflight and connector ordering are now implemented. DBFS exposes a
serialized, side-effect-free busy preflight bound to the exact inner instance;
the connector performs `operation close fence -> DBFS busy preflight ->
mount-session close -> exact device teardown`. Session validation precedes
each copied-driver dispatch, connector storage is bounded to 256 entries, and
failed post-session teardown retains a retryable slot without replaying session
close. This remains unverified by explicit instruction. The remaining trust
seam is caller-supplied nonzero device-owner identity because `BlockDevice`
still cannot derive stable identity itself.

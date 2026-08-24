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

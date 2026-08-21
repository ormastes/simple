# DBFS Durable Commit Specification

## Overview

This specification proves that device-backed DBFS acknowledges `fsync` only
through its stored block-device flush owner and reconstructs state from durable
media rather than module memory.

## Preconditions

The behavioral probe provides separate volatile and durable sector arrays.
Writes affect only volatile state; a successful flush copies it to durable
state; a power cut restores volatile state from durable state. The compact DBFS
region has at least four sectors so two checkpoint slots remain outside the
append-only data area. The device owner must also complete a checked lock/unlock
transition before a driver reports durability readiness. Provider admission
whitelists audited hosted pthread/critical-section targets. SimpleOS and unknown
providers return
`missing-simpleos-atomic-compare-exchange-or-scheduler-exclusion` and cannot
register a durable DBFS device.

## Primary Scenario

Mount device-backed DBFS through `MountTable`, create and write `/state`, and
call `fsync`. The active mount advertises `DurableSync`, the backing flush count
advances once, and a fresh driver after a simulated power cut reads the exact
committed bytes.

## Failure Scenarios

- An injected flush error makes `fsync` return `FsError.IoError`; reboot exposes
  the prior acknowledged generation.
- A newer checkpoint copied to media without its blob is rejected by the blob
  checksum; recovery falls back to the older valid slot.
- Corruption of both nonblank slots makes mount fail with `FsError.Corrupt`.
- `MemBlockDevice`, whose default flush is unavailable, cannot produce a false
  durable acknowledgement.
- Interleaved dirty/publish transitions for two device-backed instances remain
  isolated, and both reconstruct their own last acknowledged bytes after cuts.
- Passthrough and file writes share one append cursor; a passthrough prefix
  cannot be overwritten by the next checksummed file blob.
- The actual provider-classification function admits hosted Linux and rejects
  the SimpleOS/unknown provider with the stable machine-readable blocker.

## Boundaries and Limits

The compact namespace accepts at most 64 entries, paths of at most 255 bytes,
and one sector of encoded checkpoint data. The 65th entry fails with
`FsError.TooLarge` and is removed from canonical namespace state. The O(n²)
duplicate check is bounded by 64 entries and never runs on unbounded input.

## Expected Results

All nine executable scenarios use concrete values and typed errors. No scenario
uses a source-text oracle, an in-memory fallback after device read failure, or
a fabricated durability receipt.

## Reproduction

Run the admitted self-hosted Simple test runner on
`test/02_integration/storage/dbfs/dbfs_durable_commit_spec.spl`. Rust-seed or
silent stub-fallback output is not acceptable evidence.

## Traceability

- Source: `src/lib/nogc_sync_mut/db/dbfs_driver/device_commit_owner.spl`
- VFS adapter: `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl`
- Namespace operations: `src/lib/nogc_sync_mut/db/dbfs_driver/namespace_io.spl`
- Architecture: `doc/04_architecture/os/dbfs_architecture.md`
- Tracker: `doc/08_tracking/bug/simpleos_filesystem_durable_sync_barrier_gap_2026-08-20.md`
- Executable spec: `test/02_integration/storage/dbfs/dbfs_durable_commit_spec.spl`

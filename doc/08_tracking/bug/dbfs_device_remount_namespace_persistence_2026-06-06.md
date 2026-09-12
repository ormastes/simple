# DBFS Device Remount Namespace Persistence Gap

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; the previously-picked repro spec did not clearly correspond to this record's own defect, so it was not trusted, and no cheaper repro is available within budget; reopen with a fresh repro against the current seed)

Date: 2026-06-06

## Status

Implemented for the current `DbFsDriver.open_on_device` path.

## Summary

`DbFsDriver.open_on_device` now reserves the final block in its device region for a compact
namespace checkpoint. File writes persist data into the data region, record the path/inode/size and
arena offset/length in that checkpoint, and replay it into a fresh `inst_id` on the next open.

## Evidence

- `test/02_integration/storage/dbfs/dbfs_remount_persistence_spec.spl` verifies a file written on
  the first mount survives a fresh driver instance and that directory listing replays persisted
  file names.
- `test/02_integration/storage/dbfs/dbfs_driver_spec.spl` remains green for hosted DBFS behavior.
- `test/02_integration/storage/dbfs/dbfs_hw_passthrough_spec.spl` remains green for raw
  passthrough behavior.

## Required Fix

Larger follow-up work remains outside this narrow fix:

- multi-sector namespace checkpoints
- checksums/replicas
- WAL-backed namespace replay
- full DBFS recovery integration with `dbfs_engine.recovery`

## Notes

The regression spec uses `RamBlockDevice` because it implements the same stdlib `BlockDevice`
trait and exposes writes across fresh driver instances through its sector store. A
`CachedRawImageBlockDevice` variant needs care because that fixture is value-backed; writes through
a copied trait object are not visible when reopening the original value.

## Triage 2026-09-12
Remediation 2026-09-12: an earlier automated pass matched a spec path mentioned in this record and ran it, but on review that spec was not clearly this record's own reproduction (see evidence); the RESOLVED/still-reproduces verdict was withdrawn and the record was re-closed stale by age instead, without re-running an unverified repro. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

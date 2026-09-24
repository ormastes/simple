# DBFS Device Remount Namespace Persistence Gap

## Closed 2026-09-13 — Implemented for the `DbFsDriver.open_on_device` path per the entry's own status

- **inferred** The Status line records the behaviour as implemented for the current `DbFsDriver.open_on_device` path.
- **measured** All three product paths the entry references still exist (path-survival scan: 3 referenced, 0 missing), so the implementation was not later removed.
- **inferred** The dbfs spec lane cannot be executed on this host (`bin/simple test` is killed at its outer bound for every spec), so closure rests on the recorded implementation.


Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below

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

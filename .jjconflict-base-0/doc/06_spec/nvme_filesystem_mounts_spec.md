# Nvme Filesystem Mounts Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/01_unit/os/services/vfs/nvme_filesystem_mounts_spec.spl` |
| Updated | 2026-05-28 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SPipe scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |
| Logs | 5 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/unit/os/services/vfs/nvme_filesystem_mounts/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/unit/os/services/vfs/nvme_filesystem_mounts/summary.txt` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/unit/os/services/vfs/nvme_filesystem_mounts/combined.log` |
| `output.log` | Log file | `build/test-artifacts/unit/os/services/vfs/nvme_filesystem_mounts/output.log` |
| `run.log` | Log file | `build/test-artifacts/unit/os/services/vfs/nvme_filesystem_mounts/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/unit/os/services/vfs/nvme_filesystem_mounts/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/unit/os/services/vfs/nvme_filesystem_mounts/stdout.log` |

## Scenarios

- reports the lease region block count used by device-backed filesystems
- builds FAT32 from the shared lease-backed BlockDevice surface
- keeps arbitrary BlockDevice user mounts buffered unless hardware registered an NVMe adapter
- builds NVFS from the shared lease-backed BlockDevice surface
- requires committed NVFS arena bytes before exposing DirectIo extents
- builds DBFS from the shared lease-backed BlockDevice surface
- maps DBFS direct I/O file offsets onto the shared NVMe arena data region
- maps DBFS and NVFS DirectIo extents through committed arena blob offsets
- persists DBFS normal writes through the raw NVMe arena on device-backed mounts
- round-trips DBFS DirectIo-backed normal bytes from the raw NVMe arena
- does not reuse stale DBFS DirectIo arena sectors across fresh devices
- keeps FAT32 direct I/O extent mapping tied to cluster-chain storage sectors
- rejects consumers when the lease is not filesystem-ready
- rejects checked mounts that would mix system and user ownership of one namespace
- accepts checked mounts for different NVMe namespaces
- mounts root through the checked NVMe lease entry point
- rejects root mounts that would mix system and user ownership of one namespace

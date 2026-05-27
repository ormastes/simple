# Vfs Boot Nvme Lease Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl` |
| Updated | 2026-05-27 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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
| `result.json` | JSON artifact | `build/test-artifacts/unit/os/services/vfs/vfs_boot_nvme_lease/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/unit/os/services/vfs/vfs_boot_nvme_lease/summary.txt` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/unit/os/services/vfs/vfs_boot_nvme_lease/combined.log` |
| `output.log` | Log file | `build/test-artifacts/unit/os/services/vfs/vfs_boot_nvme_lease/output.log` |
| `run.log` | Log file | `build/test-artifacts/unit/os/services/vfs/vfs_boot_nvme_lease/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/unit/os/services/vfs/vfs_boot_nvme_lease/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/unit/os/services/vfs/vfs_boot_nvme_lease/stdout.log` |

## Scenarios

- builds a filesystem-ready system FAT32 lease for pure Simple boot
- keeps invalid namespace geometry rejected before FAT32 can mount
- builds production boot FAT32 leases only from ready transfer evidence
- uses hardware transfer evidence before mounting the pure Simple boot FAT32 lease
- records boot NVMe leases and rejects later user assignment of the same namespace
- assigns user namespaces through the active VFS lease registry
- creates user namespace driver instances only after active-lease admission
- routes production user namespace mounts through the pure Simple NVMe block adapter
- rejects hardware user namespace mounts before the shared boot NVMe driver is ready
- releases active user namespace leases so reassignment can proceed
- accepts only pure Simple NVMe boot storage as production-ready
- exports fail-closed production readiness through the VFS public surface

# NVFS Completion Requirements

Feature set: remaining unchecked NVFS tracker criteria.

## Functional Requirements

- REQ-NVFS-COMPLETE-001: MountTable resolve tests must exercise longest-prefix
  path stripping without `slice`.
- REQ-NVFS-COMPLETE-002: Compression must provide round-trip data, class
  defaults, incompressible fallback, and SLO evidence helpers.
- REQ-NVFS-COMPLETE-003: Offline upgrade must expose v2 pmap record length to
  v3 pmap record length conversion.
- REQ-NVFS-COMPLETE-004: Dedup must expose DEDUP tree id 12, 56-byte entry
  encoding metadata, hot-cache defaults, stats, refcount checks, and
  DHK-keyed hash behavior for encrypted datasets.
- REQ-NVFS-COMPLETE-005: spostgre E2E storage coverage must route WAL bytes
  through a MountTable-resolved RamFs path.

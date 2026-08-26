# SOSIX Positioned Filesystem Backends

Source: `test/01_unit/os/sosix/positioned_filesystem_backends_spec.spl`

Evidence class: `host-fixture` with `source-contract` routing checks.

## Scenarios

- Round-trip binary DBFS overwrites and sparse extension, and NVFS positioned
  bytes without changing the shared read position.
- Reject cross-filesystem, retired, raw, and overflowing object requests before
  driver dispatch.
- Keep colliding raw driver handles distinct behind virtual object identities.
- Publish the complete FAT32, NVFS, DBFS, and durable-sync routing matrix.

These scenarios prove backend and dispatch semantics, not physical-media boot.


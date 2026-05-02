# NVFS Completion Local Research

Feature set: FR-STORAGE-0004, FR-NVFS-N7a-001, FR-NVFS-N7b-001,
FR-STORAGE-E2E-001.

## Findings

- `MountTable.resolve` already used indexed char-copy, but its unit test still
  carried a `pass_todo` placeholder.
- `examples/nvfs/src/core/compression.spl` had round-trip compression support
  but still used tagged-copy wording and lacked explicit SLO/upgrade helpers.
- `examples/nvfs/src/core/dedup.spl` had refcount semantics, but lacked the
  DEDUP tree object id, 56-byte entry contract, default hot-cache config, stats,
  encrypted DHK-keyed hash path, and check/refcount helpers.
- `spostgre_nvfs_e2e_test.spl` mounted `/db` but documented MountTable wiring as
  a gap.

## Implementation Direction

Close the remaining NVFS acceptance criteria with focused production surfaces:
real MountTable resolve coverage, an in-repo RLE compression frame with
incompressible fallback, an offline upgrade helper, DDT metadata/stats helpers,
and a MountTable/RamFs-backed spostgre WAL byte routing scenario.

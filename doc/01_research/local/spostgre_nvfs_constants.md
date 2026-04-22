# Local Research — spostgre_nvfs_constants

Feature request: `FR-SPOSTGRE-M2-002`.

Findings:
- `examples/spostgre/src/engine/nvfs_shim.spl` locally declared `STORAGE_CLASS_DB_WAL`,
  `STORAGE_CLASS_META_DURABLE`, and `DURABILITY_DATA_DURABLE`.
- `examples/spostgre/src/engine/tier_cache.spl` locally declared `STORAGE_CLASS_DB_TEMP`.
- `examples/nvfs/src/core/arena.spl` accepts opaque `class_tag: i32` values and preserves
  them through `arena_class_impl`, but no canonical constants module existed.
- Existing spostgre tests import storage constants from the shim, while the feature request
  asks new consumers to import the canonical NVFS constants directly.

Implementation scope:
- Add `examples/nvfs/src/core/constants.spl`.
- Replace spostgre local ordinal declarations with imports.
- Add SSpec system coverage for exported ordinals and tier-cache/shim class usage.

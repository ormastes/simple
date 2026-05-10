# System Test Plan — spostgre_nvfs_constants

Specs:
- `test/system/spostgre_nvfs_constants_spec.spl`
- `examples/spostgre/test/integration/storage/spostgre_nvfs_constants_spec.spl`

Coverage:
- `STORAGE_CLASS_DB_WAL`, `STORAGE_CLASS_META_DURABLE`, `STORAGE_CLASS_DB_TEMP`, and
  `DURABILITY_DATA_DURABLE` are importable from `examples.nvfs.src.core.constants`.
- `shim_arena_create` accepts the imported WAL class and records that class on the arena.
- `tier_cache_new` creates its backing arena with imported `STORAGE_CLASS_DB_TEMP`.

Acceptance mapping:
- FR-SPOSTGRE-M2-002 AC1: constants module exports all four ordinals.
- AC2/AC3: spostgre modules no longer redeclare the ordinals.
- AC4/AC5: existing spostgre unit and storage integration tests remain green.

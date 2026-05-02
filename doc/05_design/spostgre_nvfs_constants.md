# Design — spostgre_nvfs_constants

The implementation introduces a narrow `examples/nvfs/src/core/constants.spl` module as
the canonical source for cross-submodule integer ordinals still required by arena APIs.

Constants:
- `STORAGE_CLASS_DB_WAL = 1`
- `STORAGE_CLASS_META_DURABLE = 2`
- `STORAGE_CLASS_DB_TEMP = 3`
- `DURABILITY_DATA_DURABLE = 1`

Consumers:
- `engine.nvfs_shim` imports WAL, META_DURABLE, and DATA_DURABLE constants.
- `engine.tier_cache` imports DB_TEMP.

The change deliberately avoids modifying arena storage semantics: `class_tag` remains an
opaque integer stored and returned by the arena layer.

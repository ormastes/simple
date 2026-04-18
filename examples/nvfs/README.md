# simple-nvfs

NVMe-aware filesystem (SimpleFS-NV / NVFS) for the [Simple language](https://github.com/ormastes/simple).

Hybrid copy-on-write metadata + append-oriented data classes with explicit lifetime hints and optional ZNS/FDP acceleration. Virtual storage classes: `META_DURABLE`, `DB_WAL`, `DB_TEMP`, `MODEL_IMMUTABLE`, `GENERAL_MUTABLE`, `CHECKPOINT_SNAPSHOT`. Arena API: `arena_create`, `arena_append`, `arena_readv`, `arena_seal`, `arena_discard`, `arena_clone_range`.

## Status

Skeleton — design phase. Not yet functional.

## Architecture

MDSOC-only (driver-adjacent per CLAUDE.md — no ECS business layer). Consumes NVFS trait contracts from the main Simple repo at `src/lib/nogc_sync_mut/fs/nvfs/` and the common storage traits at `src/lib/nogc_sync_mut/storage/`.

Design inputs come from two places upfront:
- `simple/doc/05_design/nvfs/from_spostgre.md` — fs requirements from the spostgre DB engine
- `simple/doc/05_design/nvfs/from_svllm.md` — fs requirements from the svllm serving tool (designed in parallel)

## Layout

```
src/
  core/       # Filesystem core — superblock, arena, extent, checkpoint, intent_log
  driver/     # NVMe runtime shim (io_uring / io_uring_cmd / VFIO backends)
test/
doc/          # Local design notes (main design lives in simple/doc/05_design/nvfs_design.md)
```

## License

UNLICENSED — license selection pending.

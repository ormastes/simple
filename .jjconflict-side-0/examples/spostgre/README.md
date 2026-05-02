# simple-spostgre

PostgreSQL-inspired database engine for the [Simple language](https://github.com/ormastes/simple), with NVMe-aware physical layout (out-of-place page updates, page-indirection map, WAL arena, temp arena, BRIN-style summaries, HOT-like updates at logical-page scope).

## Status

Skeleton — research + design phase. Not yet functional.

## Architecture

MDSOC+: an MDSOC outer capsule (modules, dependencies, side effects, capabilities, ownership) wrapping an ECS business layer (components: Relation, Page, Tuple, WalRecord, Txn, Checkpoint; systems: Commit, Vacuum, Checkpoint, BufferManager).

Common storage traits (arena, storage-class, capability-probe, durability) live in the main Simple repo at `src/lib/nogc_sync_mut/storage/`. spostgre imports those and provides concrete impls.

## Layout

```
src/
  engine/     # DB engine core — page, wal, pmap, buffer_mgr, txn, checkpoint, vacuum
  business/   # ECS components + systems
  tool/       # CLI tool (symlinked into main Simple repo at src/app/spostgre/)
test/
  unit/
  integration/
doc/          # Local design notes (main design doc lives in simple/doc/05_design/spostgre_design.md)
```

## Design docs

- `simple/doc/01_research/spostgre_research.md` — prior-art survey
- `simple/doc/05_design/spostgre_design.md` — architecture + on-disk layout + APIs
- `simple/doc/05_design/nvfs/from_spostgre.md` — fs-API contributions spostgre makes to NVFS

## License

MIT — see [LICENSE](LICENSE).

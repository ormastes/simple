# Simple DB implementations — the canonical 3-kind map

Date: 2026-08-20. Simple has exactly **three database implementations**. Every
DB-related doc, plan, or claim must say which kind it is about. Do not call
`postgres_mimic` "the DB server" — it is a compatibility surface on kind 3.

| # | Kind | One-line definition | Authoritative entry point |
|---|------|---------------------|---------------------------|
| 1 | **Textual DB** | SDN-text-file store with atomic writes + WAL; tracking DBs live here | `src/lib/nogc_sync_mut/database/core.spl` (`SdnDatabase`) |
| 2 | **Embedded DB** | In-process SQL engine (SQLite-class), pure-Simple or C SQLite via SFFI | `src/lib/nogc_sync_mut/database/pure_sql/` (`PureDatabase`) |
| 3 | **DB server** | Networked multi-user tier: sessions, deny-wins capabilities, txns, commit-before-ack durability | `std.database.server` = `src/lib/nogc_sync_mut/database/server/` |

## 1. Textual DB

SDN-text-file store; header of `core.spl` forbids manual `.sdn` edits.

| Module | Path | Role |
|---|---|---|
| Core | `src/lib/nogc_sync_mut/database/core.spl` | `SdnDatabase`/`SdnTable`/`SdnRow`, `StringInterner` |
| Durability | `database/{atomic,wal,compaction,checker}.spl` | fsync+lock atomic writes, WAL replay, integrity |
| Index/query/stats | `database/{index,query,stats,db_registry}.spl` | lookup + observability |
| Domain DBs | `database/{bug,task,todo,feature,feature_utils,feature_request_rows,requirement,test,test_extended}.spl` | tracking tables over `doc/08_tracking/**/*.sdn` |
| Search layers | `database/fts.spl`, `database/vector/` | FTS and vector index on top |
| Tier mirror | `src/lib/nogc_async_mut/database/` | async variant |
| Sibling | `src/lib/nogc_sync_mut/enterprise_store/file_backend.spl` (`SPLSTORE1`) | append-only text-line store, sqlite-free fallback behind the enterprise-store façade |

- Apps: `src/app/check_dbs/main.spl`, `src/app/cli/{check_dbs,fix_dbs}.spl`, `src/app/enterprise_store_app/`
- Tests: `test/system/database/` (db_sdn, sdn_checksum, atomic_lock_excl, atomic_fsync, wal_replay_row_materialization, requirement_db), `test/02_integration/lib/database_{core,atomic,query,e2e}_spec.spl`
- Guide: [simple_db.md](simple_db.md), [enterprise_store.md](enterprise_store.md)

## 2. Embedded DB

In-process SQL engine; four backends behind one client surface.

| Module | Path | Role |
|---|---|---|
| PureDatabase | `src/lib/nogc_sync_mut/database/pure_sql/` | pure-Simple SQL parser + MVCC storage, drop-in for `std.database.sql.Database` |
| SQL client surface | `database/sql/` | connection, pool, statement, transaction, repository, migration, query_builder |
| C SQLite via SFFI | `src/lib/{nogc,gc}_{sync,async}_mut/io/sqlite_sffi.spl` | real libsqlite3 backend (needs C toolchain) |
| VFS port | `src/os/port/sqlite/` | SimpleOS sqlite3 VFS |
| Interpreter emulation | `src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs` | `rt_sqlite_*` emulation — **non-ACID, constraints unenforced**; never cite it as ACID evidence |
| DBFS engine | `src/lib/*/db/dbfs_engine/` | pager, MVCC, B-tree, WAL, checkpoint, recovery — the embedded storage kernel (also serves the DBFS filesystem via `db/dbfs_driver/`) |
| Accelerators | `database/fast_db.spl` (C `rt_db_*` in-memory hash, no persistence), `src/lib/nogc_sync_mut/db/{query_planner,cardinality_estimator,learned_index,...}` | hot-path / optimizer layers |

- Apps/consumers: `src/app/portal/`, `src/app/llm_caret/messaging/adapter/store/pure_sql_store.spl`, `src/app/web_stack_sample/app.spl`
- Tests: `test/integration/storage/dbfs/` (~30 specs: pager, wal, mvcc_visibility, tx_protocol, recovery, checkpoint, sql_parser, pure_db), `test/05_perf/bench/pure_db_*_spec.spl`
- Guide: [sqlite_counterparts.md](sqlite_counterparts.md) (canonical counterpart map)

## 3. DB server

The authoritative multi-user enterprise tier. Enterprise production hardening
targets this kind.

| Module | Path | Role |
|---|---|---|
| Capsule | `database/server/server.spl` | MDSOC outer capsule: store port (`SdnDatabase`) + policy port + transport port |
| Tier internals | `database/server/{session,txn,capability,durability,protocol,transport}.spl` | sessions, txns, deny-wins ACL, commit-before-ack durability, framed protocol |
| PG compat surface | `database/postgres_mimic/` (+ async mirror), `src/lib/{gc_sync_mut,gc_async_mut}/spostgre_if/` | PostgreSQL wire/session compatibility — **not the server itself** |

- Apps: `src/app/postgres_mimic_server/main.spl` (PG compat), `src/app/redis_server/main.spl` (RESP key/value server — kind-3 sibling protocol server, not SQL)
- Tests: `test/03_system/database/server/{db_server_tier_spec,db_durability_spec,secure_pure_simple_db_server_spec}.spl`, hardening: `test/01_unit/lib/nogc_sync_mut/database/server/` (2026-08-20)
- Guide: [postgres_mimic_server.md](postgres_mimic_server.md) (compat surface only)

## Layers on top (not stores)

- Offload planning: `database/{db_offload,nosql_offload,query_offload,sql_join_aggregate_offload,storage_mode_offload,offload_profile,gpu_mode_plan}.spl` — GPU/RAM-SSD batch planning over kinds 1–2.
- Observability: `database/{db_metrics,db_registry}.spl`.
- Enterprise store façade: `src/lib/nogc_sync_mut/enterprise_store/store.spl` — business-level unit-of-work/idempotency/outbox over kind 2 (SQL) or the kind-1 `SPLSTORE1` file backend.

## Tier coverage

- Kind 1: `nogc_sync_mut` + `nogc_async_mut`.
- Kind 2: all four tiers for dbfs/sqlite_sffi; `pure_sql` in `nogc_*` only.
- Kind 3: `nogc_sync_mut` (+ `postgres_mimic` mirror in `nogc_async_mut`, `spostgre_if` in `gc_*`).

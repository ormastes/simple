# SQLite counterparts in Simple — what to use instead of the C library

**One-line answer: Simple has its own SQL engine in pure Simple. Use
`PureDatabase`. You do not need the C SQLite amalgamation, and you cannot use it
in-guest on SimpleOS.**

For PostgreSQL-like server sessions over this engine, use
`std.database.postgres_mimic`; see
`doc/07_guide/lib/database/postgres_mimic_server.md`. Production database use
defaults to cached SMF/LSM or native artifacts, including for interpreter-mode
callers.

This is a caller-independent policy: interpreter mode does not imply an
interpreted database. Prefer the cached SMF/LSM library for embedded reuse or a
cached native/SMF server executable for process isolation. Only an explicit
diagnostic option may execute the PureDatabase hot path from source. Readiness
metadata alone is insufficient evidence; production verification must observe
the compiled carrier being invoked.

This page exists because the C-SQLite blocker has repeatedly been mistaken for a
SQL blocker. They are different things, and the in-tree counterparts are easy to
miss.

## Pick-by-need table

| What you need | Use this (pure Simple, in-tree) | Import |
|---|---|---|
| **SQL engine** — `CREATE TABLE`/`CREATE INDEX`/`INSERT`/`SELECT`/`UPDATE`/`DELETE`/`DROP`/`WHERE`/`BEGIN`/`COMMIT`/`ROLLBACK`, plus `table_exists`, `last_insert_rowid`, `changes` | `src/lib/nogc_sync_mut/database/pure_sql/` — **`PureDatabase`**, ~4,440 lines (`_PureDatabase/pure_database.spl` + `row_value_helpers.spl`) | `use std.database.pure_sql.{PureDatabase}` |
| Embedded row store (`SdnRow`/`SdnTable`/`SdnDatabase`, pk index, `save()`, per-row `_version` optimistic locking) | `src/lib/nogc_sync_mut/database/core.spl` | `use std.database.core.*` |
| Atomic file write + advisory lock (`atomic_write` = `FileLock` + `.tmp` + `rt_file_sync` + rename) | `src/lib/nogc_sync_mut/database/atomic.spl` | `use std.database.atomic.*` |
| Write-ahead log | `src/lib/nogc_sync_mut/database/wal.spl` | `use std.database.wal.*` |
| Secondary index / full-text search | `src/lib/nogc_sync_mut/database/index.spl`, `fts.spl` | — |
| Query layer | `src/lib/nogc_sync_mut/database/query.spl` | — |
| Connection, pool, migration, repository, query-builder, escaping, health | `src/lib/nogc_sync_mut/database/sql/` | — |
| Server tier — sessions, per-session transactions, capability checks, framing, **durable commit** | `src/lib/nogc_sync_mut/database/server/` (see `durability.spl` for the house durability contract) | — |
| Filesystem-grade DB engine — pager, MVCC, B-tree, checkpoint ring, intent log, arena | `src/lib/nogc_async_mut/db/dbfs_engine/` | — |
| Offload planners (NoSQL / join-aggregate / query / storage-mode) | `src/lib/nogc_sync_mut/database/{nosql,sql_join_aggregate,query,storage_mode}_offload.spl` | — |

## What is genuinely C-SQLite, and therefore blocked

| Path | What it is |
|---|---|
| `src/lib/*/io/sqlite_sffi.spl`, `src/app/io/sqlite_ffi.spl` | SFFI wrappers over the **C** SQLite library. Need a C toolchain, link against libsqlite3, and **cannot run in-guest on SimpleOS**. |
| `src/os/port/sqlite/sqlite_vfs_contract.spl` | The `sqlite3_vfs` contract (17 methods) that a *ported* C SQLite would sit on. `xShmMap` fails closed, so WAL is honestly gated on writable shared mmap. |
| `test/*/bench/sqlite3_ground_truth.c` | A C benchmark oracle, not a dependency. |

The roadmap row "SQLite amalgamation build (multi-session, C toolchain blocked)"
refers **only** to this column. It says nothing about SQL support in Simple.

## Landmines specific to this area

- **Tier shadowing.** `use std.X` resolves families in a fixed order with
  `nogc_async_mut` **first**. `pure_sql` exists in more than one tier — confirm
  which copy actually executes before editing, or you will fix an unreachable
  file. (A shadowed `nogc_sync_mut` FAT32 tier cost 3,165 lines of double
  maintenance before it was found; the same trap applies here.)
- **The Rust seed's SQLite shim is not SQLite.** `src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs`
  implements only `CREATE TABLE` / `INSERT` / `DELETE`. Anything richer —
  `CREATE INDEX IF NOT EXISTS`, for one — fails when running on the seed. If a
  store dies in `_init_schema`, this is usually why.
- **`Some(<i64>)` returns 8×n on the JIT.** `database/core.spl`'s `get_i32` /
  `get_i64` used `Some(parsed)`, so every integer column read back eight times
  too large. Never wrap an integer in `Some` on the way out of a column read.
- **`.to_int()` never returns nil** — it is declared `i64?` but yields `0` for
  non-numeric text, so `?? default` never fires. Use `try_parse_int` from
  `src/lib/common/convert.spl` for anything parsed out of a row or a request.
- **Use a distinct file path per test.** A shared `/tmp` path makes concurrent
  spec runs contend on `FileLock` (5-minute acquire).

## Related

- Glossary entry: `doc/glossary.md` § *SQLite counterparts (pure-Simple SQL)*
- LLM wiki: `doc/00_llm_process/feature_expert/database_sql/skill.md`
- Ledger row: `database:` in `doc/08_tracking/os/production_status.sdn`
- The same "we already have it in pure Simple" pattern applies to
  **crypto** (`src/lib/common/crypto/`, `src/os/crypto/` — Ed25519 passes its
  RFC 8032 KAT) and **SSH** (`src/os/apps/sshd/`, ~9,576 lines). Check for an
  in-tree counterpart before recording an external-port blocker.

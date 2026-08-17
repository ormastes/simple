# Feature Expert: database / SQL (and the SQLite counterpart map)

## Role

Own feature-specific process knowledge for **database and SQL** work in Simple:
which module owns which capability, what is genuinely blocked on a C toolchain
versus what already exists in pure Simple, and the defects that silently corrupt
query results.

**Read this before writing any "SQLite is blocked" note.** Simple has its own SQL
engine. The C-amalgamation blocker applies only to the SFFI wrappers.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Canonical owner map

| Capability | Owner | Status |
|---|---|---|
| SQL engine (DDL/DML/`WHERE`/txn) | `src/lib/nogc_sync_mut/database/pure_sql/` → `PureDatabase`, ~4,440 lines | pure Simple, in-tree |
| Row store | `database/core.spl` (`SdnDatabase`/`SdnTable`/`SdnRow`) | pure Simple |
| Atomic write + lock | `database/atomic.spl` (`atomic_write`, `FileLock`) | pure Simple |
| WAL | `database/wal.spl` | pure Simple; **no txn-boundary record**, so an entry-by-entry append is torn by a mid-run crash |
| Index / FTS / query | `database/{index,fts,query}.spl` | pure Simple |
| Client surface (connection, pool, migration, repository, query-builder, escaping) | `database/sql/` | pure Simple |
| Server tier (sessions, txn scoping, capability, framing, durable commit) | `database/server/` incl. `durability.spl` | pure Simple; in-process model, no listener bound |
| DB filesystem engine (pager, MVCC, B-tree, checkpoint) | `src/lib/nogc_async_mut/db/dbfs_engine/` | pure Simple |
| **C SQLite via SFFI** | `src/lib/*/io/sqlite_sffi.spl`, `src/app/io/sqlite_ffi.spl` | **needs a C toolchain; cannot run in-guest** |
| `sqlite3_vfs` contract for a ported C SQLite | `src/os/port/sqlite/sqlite_vfs_contract.spl` | contract; `xShmMap` fails closed → WAL gated on writable shared mmap |

## Feature Links

- Guide (canonical map): [doc/07_guide/lib/database/sqlite_counterparts.md](../../../07_guide/lib/database/sqlite_counterparts.md)
- Glossary: `doc/glossary.md` § *SQLite counterparts (pure-Simple SQL)* and § *In-Tree Counterpart Rule*
- LLM aliases and deployment defaults: `doc/00_llm_process/llm_wiki.md`.
- PostgreSQL-like session/query compatibility: `std.database.postgres_mimic`,
  backed by `PureDatabase` without SFFI.
- Production DB hot paths use cached SMF/LSM or native artifacts even when an
  interpreter-mode tool launches them.
- Ledger row: `database:` in `doc/08_tracking/os/production_status.sdn`
- Source: `src/lib/nogc_sync_mut/database/`, `src/lib/nogc_async_mut/db/dbfs_engine/`, `src/os/port/sqlite/`

## Durability contract (established, follow it)

`src/lib/nogc_sync_mut/database/server/durability.spl` is the house pattern:
precheck → undo pre-images → apply to memory → persist via `save()`
(`atomic_write` = `FileLock` + `.tmp` + `rt_file_sync` + rename) → ack.
**The commit point is the rename.** Stated non-guarantees: `_version` is not
serialized, undeclared columns are not durable, durability is per-COMMIT not
per-PUT, and a crash after persist but before ack is at-least-once.

## Known constraints and landmines

- **Tier shadowing:** `use std.X` resolves `nogc_async_mut` **first**. `pure_sql`
  exists in more than one tier — confirm which copy executes before editing, or
  you will fix an unreachable file.
- **The seed's SQLite shim is not SQLite:** `src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs`
  implements only CREATE TABLE / INSERT / DELETE. `CREATE INDEX IF NOT EXISTS`
  fails on the seed — the usual cause of a store dying in `_init_schema`.
- **`Some(<i64>)` is 8×n on the JIT.** `core.spl`'s `get_i32`/`get_i64` used
  `Some(parsed)`, so every integer column read back eight times too large. Never
  wrap an integer in `Some` on a column-read path.
- **`.to_int()` never returns nil** (declared `i64?`, yields `0`), so `?? default`
  never fires and non-numeric text parses as `0` — fail-open. Use `try_parse_int`
  from `src/lib/common/convert.spl`.
- **`x.f += v` drops the operator entirely** — write `x.f = x.f + v`.
- **A module-global written in a function is invisible to helpers it then calls**
  (commits on return) — build in a local, publish once.
- Use a distinct file path per test; a shared `/tmp` path makes concurrent specs
  contend on `FileLock`.

## Verification commands

```
bin/simple run test/01_unit/os/port/sqlite_vfs_contract_spec.spl
bin/simple run test/system/database/server/db_durability_spec.spl
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <same spec>   # always A/B
```
sspec prints one `"N examples, M failures"` line **per describe block** — check
every line. Never run whole-suite `simple test`.

## Update Rule

When database/SQL research, requirements, architecture, design, tests,
implementation, verification, or release artifacts change, update this skill with
the new links and current handoff notes — and re-check the owner map above, since
its whole purpose is to stop the next session re-deriving "SQLite is blocked".

## Seed sqlite-emulation fixes (2026-08-17)

`208f11786f8` fixed three seed-emulation gaps: `DELETE ... WHERE` now honors
the predicate (fail-closed instead of deleting all rows), `BEGIN`/`ROLLBACK`
take real snapshots, and `UNIQUE` constraints are enforced. Related runtime
fixes: SQL strings are NUL-terminated before reaching sqlite (`8d04ee87582`),
and real sqlite is linked for AOT native builds (`1f4121930a8`). If a spec
passed only because emulation ignored WHERE or UNIQUE, it may go red now —
that is the fix working, not a regression.

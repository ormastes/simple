# Simple DB Guide

Simple DB is a two-tier database system written in Simple:

- **Simple DB Embedded** (stdlib) — lightweight embedded database for compiler metadata, project tracking, and application-level key-value/table storage. Ships with every Simple installation. Uses SDN format with atomic file I/O.
- **Simple DB Full** (historical example) — its submodule history is recoverable,
  but the recorded implementation is an unfinished skeleton with `pass_todo`;
  it is not a working server and is not present in the current worktree.

The embedded and planned full tiers share `simple_db_if`. SimpleOS now has a
bounded persistent boot-service core at
`src/os/services/database/simple_db_service.spl`. The existing boot HTTP
listener routes `POST /db` bodies through `CREATE table`,
`INSERT table key value`, and `SELECT table key`; other web requests keep the
existing response path. One module-owned literal store persists across accepted
connections. Request bodies clamp to the 1024-byte boot cap, and responses use
connection-close framing so RV64 never computes the broken negative
`Content-Length`. This source path is not a live-QEMU claim. The canonical RV64
gate must return the inserted `codex-41` value; readiness strings alone still
fail.

```
┌──────────────────────────────────────────────────┐
│              Simple DB Full (example)             │
│  MVCC · WAL · TOAST · Checkpoint · Vacuum        │
│  Buffer pool · Page indirection · Arena storage  │
├──────────────────────────────────────────────────┤
│           simple_db_if (shared traits)            │
│  StorageApi · Transaction · BufferFrame · Pmap   │
├──────────────────────────────────────────────────┤
│           Simple DB Embedded (stdlib)             │
│  SDN tables · QueryBuilder · Atomic I/O          │
│  BugDB · TestDB · FeatureDB · StringInterner     │
└──────────────────────────────────────────────────┘
```

## Quick Start — Embedded

```simple
use std.database.bug.{create_bug_database, Bug, BugSeverity, BugStatus}
use app.io.{rt_timestamp_now}

val db = create_bug_database("my_bugs.sdn")

val bug = Bug(
    id: "BUG-001",
    title: "Example bug",
    severity: BugSeverity.P1,
    status: BugStatus.Open,
    description: ["First bug report"],
    file: "src/example.spl",
    line: 42,
    reproducible_by: "test/example_spec.spl",
    fix_strategy: [],
    investigation_log: [],
    created_at: rt_timestamp_now(),
    updated_at: rt_timestamp_now(),
    valid: true
)

db.add_bug(bug)
db.save()
```

## Architecture

### Embedded (stdlib)

Lightweight table storage for compiler metadata and app-level data. No server, no buffer pool — just atomic file I/O over SDN files.

```
┌─────────────────────────────────────┐
│      Simple DB Embedded             │
│                                     │
│  SDN Parser/Serializer              │
│  StringInterner (20-40% savings)    │
│  SdnTable / SdnRow                  │
│  QueryBuilder (filter/sort/limit)   │
│  Atomic I/O (shared read, excl write)│
│                                     │
│  Domain DBs:                        │
│    BugDatabase                      │
│    TestDatabase                     │
│    FeatureDatabase                  │
│    TodoDatabase (read-only)         │
│    TaskDatabase (read-only)         │
└─────────────────────────────────────┘
```

### Full Engine (example)

PostgreSQL-compatible storage engine. Follows **MDSOC+** (capsule boundary + internal ECS). Reuses stdlib SDN/QueryBuilder/atomic primitives for metadata; adds transactional page storage on NVFS.

```
┌─────────────────────────────────────┐
│      Simple DB Full Capsule         │
│  ┌───────────────────────────────┐  │
│  │         ECS World             │  │
│  │                               │  │
│  │  Entities:                    │  │
│  │    Transaction, BufferFrame   │  │
│  │    PmapBinding, BlobRef       │  │
│  │    CapabilityView             │  │
│  │                               │  │
│  │  Systems:                     │  │
│  │    sys_commit, sys_wal_flush  │  │
│  │    sys_checkpoint, sys_vacuum │  │
│  │    sys_buffer_evict           │  │
│  │    sys_pmap_publish           │  │
│  │    sys_blob_gc                │  │
│  │    sys_capability_probe       │  │
│  └───────────────────────────────┘  │
│              │                      │
│       ┌──────┴──────┐               │
│       │    NVFS     │               │
│       │   Arenas    │               │
│       └─────────────┘               │
└─────────────────────────────────────┘
```

### Shared Interface (`simple_db_if`)

The `simple_db_if` trait surface in stdlib defines the contract between embedded and full tiers. Both tiers implement these traits, so application code can target the interface and swap backends:

```simple
use std.simple_db_if.{StorageApi, PageRef, TxHandle}

fn write_record(storage: StorageApi, data: [u8]):
    val tx = storage.begin()
    storage.put(tx, "key", data)
    storage.commit(tx)
```

- Embedded backend: SDN file storage (single-process, no concurrency)
- Full backend: MVCC page storage with WAL (multi-client, crash-safe)

Trait surfaces: `src/lib/nogc_sync_mut/simple_db_if/`, `src/lib/gc_async_mut/simple_db_if/`

### Full Engine Storage Model

- **Pages**: 8 KiB, never updated in place on flash
- **Writes**: Append new physical page → atomically bump page-indirection map (`rel.pmap`)
- **MVCC**: PostgreSQL-compatible `xmin`/`xmax` with HOT chains
- **Durability**: WAL-first with arena-based checkpointing
- **TOAST**: Out-of-line storage for large values

### Milestones

| Milestone | Runtime Target | Description |
|-----------|---------------|-------------|
| M1-M2 | `nogc_sync_mut` | Synchronous mutable, no GC |
| M3+ | `nogc_async_mut` | Hot paths graduate to async I/O |

## Embedded Database Modules (stdlib)

The standard library provides specialized databases built on the shared SDN/QueryBuilder/atomic foundation. These are the **embedded tier** — no server required, usable from any Simple program:

### BugDatabase

Track compiler bugs with severity and status metadata.

```simple
use std.database.bug.{create_bug_database, load_bug_database, Bug, BugSeverity, BugStatus}

val db = create_bug_database("bugs.sdn")
db.add_bug(bug)
val critical = db.query_by_severity(BugSeverity.P0)
val open = db.query_by_status(BugStatus.Open)
db.save()
```

### TestDatabase

Track test execution results, timing, and flakiness.

```simple
use std.database.test.{create_test_database, TestResult, TestStatus, RunStatus}

val db = create_test_database("tests.sdn")
val run_id = db.start_run()
db.add_result(run_id, result)
db.end_run(run_id, RunStatus.Completed)
db.save()
```

### FeatureDatabase

Track feature implementation across compilation modes (Pure, Hybrid, LLVM).

```simple
use std.database.feature.{create_feature_database, Feature, FeatureStatus, FeatureMode}

val db = create_feature_database("features.sdn")
db.add_feature(feature)
db.update_feature("generics", updated_feature)
db.save()
```

## QueryBuilder

Advanced filtering, sorting, and limiting across any SDN table:

```simple
use std.database.query.{QueryBuilder, CompareOp}

var query = QueryBuilder.for_table(table)
query.filter_by("severity", CompareOp.Eq, "P0")
query.filter_by("status", CompareOp.Eq, "Open")
query.order_by("id", desc: false)
query.take(10)
val results = query.execute()
```

## Atomic File I/O

All database operations use atomic file I/O to prevent corruption:

- **Read**: `atomic_read(path)` — shared lock, multiple readers allowed
- **Write**: `atomic_write(path, content)` — write-rename pattern with exclusive lock
  1. Write to temporary file (`path.tmp`)
  2. Acquire exclusive lock on final path
  3. Atomic rename (tmp -> final)
  4. Release lock

**Rule**: NEVER manually edit `.sdn` files or use `file_write()` on database paths. Always use the database API.

## SDN Format

Simple Data Notation (SDN) is the storage format — human-readable and version-control-friendly. Features:

- **StringInterner**: Repeated strings stored once (20-40% space savings)
- **SdnTable/SdnRow**: In-memory table representation
- **Soft deletion**: `valid=false` flag, never hard delete
- **Timestamps**: ISO 8601 format (YYYY-MM-DD HH:MM:SS)
- **Keys**: String-based (human readable, no integer IDs)

## DBFS (Database Filesystem)

DBFS is a filesystem that uses database techniques to manage metadata and file nodes (like btrfs uses B-trees). Because it uses DB-like data structures internally (B-tree, WAL, pager), it also provides a DB-optimized storage path that Simple DB Full can leverage — sharing primitives rather than duplicating them. Key components:

- B-tree indexing (`test/02_integration/storage/dbfs/dbfs_engine_btree_spec.spl`)
- WAL journaling (`test/02_integration/storage/dbfs/dbfs_engine_wal_spec.spl`)
- Page-level checkpointing (`test/02_integration/storage/dbfs/dbfs_engine_checkpoint_spec.spl`)
- Intent logging (`test/02_integration/storage/dbfs/dbfs_engine_intent_log_spec.spl`)
- NVMe passthrough (`test/02_integration/storage/dbfs/dbfs_nvme_callback_spec.spl`)
- Capability-based access control (`test/02_integration/storage/dbfs/dbfs_capability_spec.spl`)
- Power-cut recovery (`test/02_integration/storage/dbfs/dbfs_recovery_spec.spl`)

## Shared Acceleration (SIMD)

Simple DB includes shared SIMD-accelerated primitives for scan and bitmap operations. See `doc/05_design/simple_db_shared_accel_simd.md`.

## Project Layout

```
# ── Shared Interface (simple_db_if) ──────────────────────────────
src/lib/nogc_sync_mut/simple_db_if/  # trait surfaces (StorageApi, types)
src/lib/nogc_async_mut/simple_db_if/ # async variant
src/lib/gc_async_mut/simple_db_if/   # GC-friendly facades
src/lib/gc_sync_mut/simple_db_if/    # GC sync facades

# ── Embedded Tier (stdlib) ───────────────────────────────────────
src/lib/nogc_sync_mut/database/      # BugDB, TestDB, FeatureDB, QueryBuilder, atomic I/O
src/lib/nogc_sync_mut/db_atomic.spl  # atomic DB operations
src/lib/nogc_async_mut/db_atomic.spl # async atomic DB operations
src/lib/gc_sync_mut/db/              # GC-based DB compat layer
src/lib/gc_sync_mut/io/sqlite_sffi.spl  # SQLite FFI bindings

# ── Full Tier (example submodule) ────────────────────────────────
examples/11_advanced/simple_db/                   # full engine (MVCC, WAL, TOAST, buffer pool)

# ── Tests ────────────────────────────────────────────────────────
test/02_integration/storage/dbfs/                            # DBFS test suite (28+ specs)
test/03_system/db_sdn_spec.spl           # embedded tier SDN spec
test/03_system/simple_db_nvfs_constants_spec.spl  # full tier NVFS constants
```

## Related Documentation

| Document | Path |
|----------|------|
| Research report | `doc/01_research/simple_db_research.md` |
| Engine design | `doc/05_design/simple_db_design.md` |
| NVFS requirements | `doc/05_design/nvfs/from_simple_db.md` |
| Accel/SIMD design | `doc/05_design/simple_db_shared_accel_simd.md` |
| DB access enforcement | `doc/05_design/database_access_enforcement_design.md` |
| DB synchronization | `doc/05_design/database_synchronization_implementation.md` |
| Unified DB design | `doc/05_design/unified_database_design.md` |
| Feature requests | `doc/08_tracking/feature/simple_db_requests.md` |
| Glossary | `doc/glossary.md` (see: Simple DB, DBFS, SDN) |

## CRUD Performance Compare

Use the repo wrapper for embedded-vs-baseline CRUD checks:

```bash
sh scripts/check/check-simple-db-perf-compare.shs
```

Strict mode is the release gate:

```bash
sh scripts/check/check-simple-db-perf-compare.shs --strict
```

The wrapper writes:

- `doc/09_report/perf/simple_db_mode_compare_2026-06-21.md`
- `doc/10_metrics/perf/simple_db_mode_compare.md`
- `doc/09_report/perf/db_crud_sqlite_postgres_compare_2026-06-21.md`
- `doc/10_metrics/perf/db_crud_sqlite_postgres_compare.md`

Strict pass requires validated embedded rows to meet both SQLite and
PostgreSQL baseline rows, no interpreter fallback, and measured full/server
mode. Set `SIMPLE_DB_SERVER_BENCH_CMD` to a full/server benchmark command when
the full engine checkout is available.

Current blocker evidence is tracked in
`doc/08_tracking/bug/simple_db_perf_native_server_blockers_2026-06-21.md`.

## Example Repository

The full engine implementation lives in a separate git submodule:

```
examples/11_advanced/simple_db/  →  https://github.com/ormastes/simple-simple_db.git
```

Clone with submodules:
```bash
git clone --recurse-submodules https://github.com/ormastes/simple.git
# or if already cloned:
git submodule update --init examples/11_advanced/simple_db
```

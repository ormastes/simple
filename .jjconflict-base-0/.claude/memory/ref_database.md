---
name: Database Library Reference
description: BugDatabase, TestDatabase, FeatureDatabase API, query builder, SDN format, atomic ops
type: reference
---

## Architecture
`Domain DBs (Bug/Test/Feature) → QueryBuilder → SdnDatabase → AtomicOps → SDN files`

## Core API (`lib.database.mod`)
- `StringInterner.empty()` — O(1) intern/lookup, bidirectional string↔ID
- `SdnRow.empty()` — `.set(k,v)`, `.get(k)`, `.get_i64(k)`, `.get_bool(k)`
- `SdnTable.new(name, [cols])` — `.add_row()`, `.get_row(id)`, `.mark_deleted()`, `.valid_rows()`
- `SdnDatabase.new(path)` / `.load(path)` — `.get_table()`, `.get_table_mut()`, `.set_table()`, `.save()`
- **CRITICAL:** After `get_table_mut()`, MUST `set_table()` to put it back

## Query Builder (`lib.database.query`)
```simple
QueryBuilder(db, "users")
    .filter_by("status", CompareOp.Eq, "active")
    .filter_by("age", CompareOp.Gt, "18")
    .only_valid().order_by("created_at", desc: true).take(10).execute()
```
Ops: `Eq`, `Gt`, `Lt`, `Contains`. Methods: `filter_in()`, `only_valid()`, `order_by()`, `take()`

## BugDatabase (`lib.database.bug`)
- `create_bug_database(path)` / `load_bug_database(path)`
- Queries: `.all_bugs()`, `.open_bugs()`, `.critical_bugs()`, `.bugs_by_severity(P0)`, `.bugs_by_status(Open)`
- Stats: `.stats()` → `.total`, `.open`, `.health`
- Severities: P0/P1/P2/P3/Important. Statuses: Open/Investigating/Confirmed/Fixed/Closed/Wontfix

## Atomic Ops (`lib.database.atomic`)
- `atomic_write(path, content)`, `atomic_read(path)`, `atomic_append(path, line)`
- `FileLock(resource, lock_path, locked_at)` — 2hr stale timeout

## Tests
- `bin/simple test/lib/database_spec.spl` (27 tests)
- `test/integration/database_*.spl` (80+ integration tests)

## Limitations
- No indexes (linear scan), no ACID transactions, last-write-wins concurrency

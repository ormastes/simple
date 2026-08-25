# Pure-Simple SQL: re-opening an already-checkpointed file stack-overflows — 2026-08-25

Status: OPEN. Tier: EMBEDDED (`std.database.pure_sql`,
`src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl`).
Found while fixing
`llm_caret_pure_sql_where_text_pk_returns_no_rows_2026-08-25.md`; a different
defect, not fixed there.

## Reproduce

Script: `PureDatabase.open_deferred(path)` -> `CREATE TABLE IF NOT EXISTS mm
(id TEXT PRIMARY KEY, value TEXT NOT NULL)` -> INSERT one row ->
`checkpoint()`. First run on a fresh path: fine. Second run of the same script
on the SAME path (file now holds the checkpointed content):

```
thread 'simple-main' (670999) has overflowed its stack
fatal runtime error: stack overflow, aborting
```

Binary: `bin/release/x86_64-unknown-linux-gnu/simple 60650360 2026-08-23
04:47:05 +0000` (Rust seed). The affected llm_caret specs dodge it only
because they `file_delete` the path first. Suspect: the `_load_from_disk` /
restore path (~`:1061`, `:1640`); not bisected yet.

## Unblock condition

Opening an existing checkpointed file must load it (or return `Err`), never
abort. Ship the fix with a reproduce case next to
`test/01_unit/lib/database/pure_sql_select_cache_spec.spl`.

## Narrowing (2026-08-25, post cache-fix)

Re-verified after the SELECT-cache fix landed locally: still aborts, rc=134,
2/2 runs on the same `t.db` (`/mnt/data/tmp/claude-1000/sql_reopen_{1,2}.log`),
so it is independent of that defect. **The minimal sequence in "Reproduce" is
NOT sufficient on its own**: `pure_sql_select_cache_spec.spl`'s deferred-file
case does `open_deferred` -> `CREATE TABLE IF NOT EXISTS mm (id TEXT PRIMARY
KEY, value TEXT, n INTEGER)` -> DELETE -> INSERT -> `checkpoint()` on the fixed
path `/tmp/pure_sql_select_cache_spec.db` and reopened that checkpointed file
cleanly on runs 2 and 3. The two schemas differ in `value TEXT NOT NULL`
(overflowing) vs `value TEXT` (fine) and in `CREATE TABLE` vs `CREATE TABLE IF
NOT EXISTS` on an existing table. Start the bisect there — the persisted
column-constraint text is the leading suspect for a recursion in the
reload/parse path. Reproducer script:
`/mnt/data/tmp/claude-1000/sqlrepro/repro.spl` (run twice on the same path).

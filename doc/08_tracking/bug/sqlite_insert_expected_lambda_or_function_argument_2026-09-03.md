# `sqlite_insert(...)` fails to compile: "expected lambda or function argument"

- **Date:** 2026-09-03
- **Severity:** MEDIUM — blocks every SQLite write path on the Rust seed
- **Binary:** Rust seed `bin/simple.exe`, `Simple Language v1.0.0-rc.1`
- **Platform:** measured on Windows; not verified on Linux.

## Symptom

Any call to `sqlite_insert` is rejected at semantic analysis. Six-line repro,
run against a pristine tree:

```
use app.io.sqlite_sffi.{sqlite_open_memory, sqlite_execute, sqlite_insert, sqlite_close}
val db = sqlite_open_memory()
sqlite_execute(db, "CREATE TABLE t (a TEXT, b TEXT)")
val n = sqlite_insert(db, "t", ["a", "b"], ["x", "y"])
print("rowid=" + n.to_string())
sqlite_close(db)
```

```
error: semantic: expected lambda or function argument
```

exit 1. The call matches the declared signature exactly:
`fn sqlite_insert(conn: SqliteConnection, table: text, columns: [text], values: [text]) -> i64`
(`src/lib/nogc_sync_mut/io/sqlite_sffi.spl:491`). Sibling calls in the same
module — `sqlite_open_memory`, `sqlite_execute`, `sqlite_query_all`,
`sqlite_close` — all work. Reformatting the call (single line vs. multi-line,
with/without trailing comma, hoisting the two array literals into `val`s)
changes nothing.

## Isolation

Found while restoring `context_sql_put_pack` to `src/app/io/context_ops.spl`.
Bisected by stubbing that function's body and re-adding statements: everything
compiles and runs (`_context_sql_open`, `_context_sql_schema`,
`_context_sql_literal`, `_context_normalize_target`, `_context_line_count`,
`_context_token_estimate`, `sqlite_execute`, `sqlite_close`) except the
`sqlite_insert` line. Reproduces on the pristine tree with the script above, so
it is not caused by that restore.

## Impact

`spipe_context_sql_put` in the SPipe MCP server aborts the serve loop: a
17-request JSONL session answers only the first 10 requests and exits 1.
`context_sql_index_packs` and `context_sql_query_packs_by_source` reach
`sqlite_insert` on their path-ingest branch and are expected to fail the same
way. The read-side (`context_sql_get_pack`) is unaffected and runs clean.

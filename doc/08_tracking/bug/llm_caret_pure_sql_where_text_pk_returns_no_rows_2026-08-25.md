# Pure-Simple SQL store: `WHERE id = 'schema_version'` returns 0 rows although the row exists — 2026-08-25

Status: FIXED 2026-08-25 (see "FIXED" section at the bottom). Was: OPEN (P1) — reproduces on BOTH the fresh seed (origin/main
`684fadabcae`) and the deployed 2026-08-23 seed, so it is not a seed-parity
issue. Engine: `std.database.pure_sql` (`src/lib/nogc_sync_mut/database/**`),
consumer: `src/app/llm_caret/messaging/adapter/store/pure_sql_store.spl`.

## Affected specs

| spec | Results: | first failing assertion |
|---|---|---|
| `test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl` | `10 total, 6 passed, 4 failed` | `store.schema_version()` — `expected 0 to be greater than 0` |
| `test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl` | `3 total, 0 passed, 3 failed` (both seeds, two consecutive runs) | `store.ready()` — `expected false to equal true` |

The other failures in those specs (`expected 0 to equal 1` for a repeated
idempotency key, `expected true to equal false` for inbound dedup,
`expected  to equal artifact-1`, dead-letter count) are all lookups by a TEXT
primary key through the same engine.

## Probe (spec on the fresh seed)

After `PureSqlMessagingStore.open(path)` on a freshly deleted file:

```
SELECT id, value FROM messaging_metadata            -> 1 row: id=[schema_version] value=[1]
SELECT value FROM messaging_metadata WHERE id = 'schema_version'   -> 0 rows   (run 1)
                                                                    -> 1 row    (run 2, same code)
SELECT value FROM messaging_metadata WHERE id = ?   ["schema_version"] -> 1 row
SELECT value FROM messaging_metadata WHERE value = '1'              -> 1 row
SELECT ... WHERE id == 'schema_version'             -> DbError::QueryFailed(parse error)
```

`pure_sql_store.spl:294` (initialize) and `:315` (`schema_version()`) both use
the literal-equality form. The answer is not stable across runs of the same
probe: the first run returned 0 rows for every literal lookup and the second
returned 1. The store's `open()` (`:272-280`) runs `initialize()`, then
`checkpoint()` and `set_auto_checkpoint(true)` — the intermittency points at
the deferred-open / checkpoint state of `PureDatabase.open_deferred` rather
than at SQL parsing (the parameterised form was never observed to fail).

## Unblock condition

`std.database.pure_sql` must answer a literal `WHERE <text_pk> = '<value>'`
identically to the `?`-bound form and identically before/after the first
checkpoint. Re-verify with
`bin/simple test test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl`
(reproduce) then `…/llm_caret_messaging_primitive_spec.spl` (similar cases).

## FIXED 2026-08-25 — stale per-table SELECT result cache, not SQL parsing

Status: FIXED. Tier: EMBEDDED pure-Simple SQL engine
(`std.database.pure_sql`, `src/lib/nogc_sync_mut/database/pure_sql/**`;
see `doc/07_guide/lib/database/db_implementations_map.md`). Binary identity
for every run below: `bin/release/x86_64-unknown-linux-gnu/simple 60650360
2026-08-23 04:47:05 +0000` (the Rust seed; clean worktree uses the same build).

### Root cause

`PureDatabase.query()` (`_PureDatabase/pure_database.spl` ~1274-1294) keeps a
**single-slot, per-table result cache for parameter-free SELECTs**, keyed by
the SQL text only (`_sel_cache_key[ti]` / `_sel_cache_res[ti]`). The plain
`_do_insert` path committed the row, flipped `_tbl_all_visible`, and marked
dirty — but never cleared that slot (the UPSERT/UPDATE/DELETE paths do, via
`_invalidate_fts`). `checkpoint()` does not clear it either.

The store's `initialize()` runs
`SELECT value FROM messaging_metadata WHERE id = 'schema_version'` (0 rows,
cached), then INSERTs the row, then `schema_version()` re-issues the
byte-identical SQL and is served the stale 0-row result. Every symptom in the
probe follows:

- the `?`-bound form always worked because `params.len() != 0` bypasses the cache;
- `WHERE value = '1'` worked because it is a different SQL text (cache miss);
- "run 1 -> 0 rows, run 2 -> 1 row" was ordering, not nondeterminism: the
  slot holds one entry per table, so any other parameter-free query on the
  table (e.g. the probe's `SELECT id, value FROM messaging_metadata`) evicts
  the stale entry and the next literal lookup re-scans. Probe order decided
  the answer. Literal tokenizing/quoting, `_parse_literal`, the pk hash map
  and MVCC visibility were all read and are sound.

### Fix

`_do_insert`: when `inserted > 0`, clear the table's `_sel_cache_*` and
`_scan_cache_*` slots (mirrors the typed-API insert reset at ~:566/:589). The
FTS index is maintained incrementally in that path and is deliberately NOT
invalidated, so no perf or architecture change. One hunk, engine-only;
`src/app/llm_caret/**` untouched.

### Reproduce + similar cases

New engine spec `test/01_unit/lib/database/pure_sql_select_cache_spec.spl`
(memory DB, plus one `open_deferred` file case across `checkpoint()`):
byte-identical text-pk literal SELECT across INSERT, same across checkpoint,
literal with spaces, `''` escaped quote, non-pk text column, integer literal,
bound-vs-literal parity.
Pre-fix: `Results: 7 total, 0 passed, 7 failed` (every case `expected 0 to equal 1`).
A spec that INSERTs *before* the first literal SELECT passes even without the
fix — the miss-then-insert-then-identical-SQL order is load-bearing.

### Evidence (post-fix, 3 runs each; logs `/mnt/data/tmp/claude-1000/sql_*.log`)

| spec | run 1 | run 2 | run 3 |
|---|---|---|---|
| `test/01_unit/lib/database/pure_sql_select_cache_spec.spl` (shared tree) | `Results: 7 total, 7 passed, 0 failed` | same | same |
| `test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl` (shared tree) | `Results: 3 total, 3 passed, 0 failed` | same | same |
| `test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl` (clean worktree `/mnt/data/tmp/claude-1000/caret-clean`, fix copied in) | `Results: 10 total, 10 passed, 0 failed` | same | same |

Pre-fix in this session: store spec `Results: 3 total, 0 passed, 3 failed`
(`expected false to equal true`), matching the table at the top.
Lint: `PASS — 1 file(s) checked` for both changed files.

### Found alongside, NOT fixed here

Re-opening an already-checkpointed `open_deferred` file (second run of the
same script on the same path) aborts with `thread 'simple-main' has
overflowed its stack`. Separate defect in the reload path; filed as
`doc/08_tracking/bug/pure_sql_reopen_checkpointed_file_stack_overflow_2026-08-25.md`.

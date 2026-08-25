# Pure-Simple SQL store: `WHERE id = 'schema_version'` returns 0 rows although the row exists — 2026-08-25

Status: OPEN (P1) — reproduces on BOTH the fresh seed (origin/main
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

# SQL savepoint names were interpolated raw into SQL text (multi-statement injection)

- **Date:** 2026-08-08
- **Severity:** High (SQL injection)
- **Status:** FIXED
- **Area:** `src/lib/nogc_sync_mut/database/sql/`

## Summary

`Transaction.savepoint`, `Transaction.release_savepoint`, and
`Transaction.rollback_to` placed a caller-supplied savepoint name directly into
SQL text with no validation and no quoting:

- `src/lib/nogc_sync_mut/database/sql/transaction.spl:65` — `val sql = "SAVEPOINT {name}"`
- `src/lib/nogc_sync_mut/database/sql/transaction.spl:80` — `val sql = "RELEASE SAVEPOINT {name}"`
- `src/lib/nogc_sync_mut/database/sql/transaction.spl:95` — `val sql = "ROLLBACK TO SAVEPOINT {name}"`

These three were the only identifier paths in the whole `database/sql/` package
that skipped `escape.quote_ident`. `query_builder.spl`, `repository.spl`,
`schema.spl`, and `sql_gen.spl` all quote their table and column identifiers.
`escape.spl` already exported both `quote_ident` and `validate_ident`; the
savepoint family simply never called them.

## Why it is high severity

The statement is dispatched through `sqlite_execute` →
`rt_sqlite_execute`. The **native runtime implementation** of that primitive is
`sqlite3_exec`:

- `src/runtime/runtime_sqlite.c:91` — `int rc = sqlite3_exec(db, s, NULL, NULL, &err);`

`sqlite3_exec` executes **every** `;`-separated statement in the string. A
savepoint name of `sp1; DROP TABLE users; --` therefore appends a `DROP TABLE`
to the caller's transaction. Savepoint names are exactly the kind of value
applications derive from request ids, tenant names, or retry labels, so this is
a reachable sink, not a theoretical one.

## Reproduction caveat (read before re-testing)

The defect is **not reproducible on the `bin/simple test` path**, and that is a
property of the harness, not of the defect. `bin/simple` is currently the Rust
bootstrap seed, whose in-process SQL engine
(`src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs:1166`,
`rt_sqlite_execute_fn` → `sqlite_execute_statement`) is **single-statement** —
splitting on `;` is done only by the separate `rt_sqlite_execute_batch_fn`
(same file, line 1178). The seed therefore rejects the whole payload as an
unparseable statement instead of executing the smuggled `DROP`.

An early probe in this investigation appeared to show the `DROP` succeeding, via
a `SELECT name FROM sqlite_master WHERE type = 'table' AND name = 'victim'`
oracle returning 0 rows. **That oracle was wrong** — the seed's engine returns 0
rows for that query regardless. Querying the table directly
(`SELECT id FROM victim`) showed the table intact. Do not reuse the
`sqlite_master` oracle on the seed path.

The multi-statement severity above rests on source inspection of
`runtime_sqlite.c:91`, which is primary-source and unambiguous, not on a
demonstrated `DROP`.

## Fix

`src/lib/nogc_sync_mut/database/sql/transaction.spl` now validates and quotes
the name before any SQL is constructed, via a new module-level helper:

```
fn _savepoint_ident(name: text) -> Result<text, DbError>:
    val checked = validate_ident(name)
    if val Err(msg) = checked:
        return Err(DbError.TransactionFailed("invalid savepoint name: {msg}"))
    Ok(quote_ident(name))
```

All three call sites now do `val ident = _savepoint_ident(name)?` and
interpolate `{ident}`. `validate_ident` restricts the name to `[A-Za-z0-9_]`
and a 64-character maximum; `quote_ident` then double-quotes it. Rejection
happens **before** the SQL string exists, so nothing reaches the engine.

No `savepoint_safe()` variant was added alongside the unsafe one — that is the
`sql_raw` / `sql_raw_safe` pattern already present in this package, and leaving
a vulnerable path live is how this hole survived.

## Verification

Engine: **interpreter path only** (`bin/simple test`). `bin/simple` prints the
Rust-bootstrap-seed banner, so this does NOT prove JIT, native, or self-hosted
behaviour.

Regression spec:
`test/01_unit/lib/database/sql/sql_transaction_savepoint_injection_spec.spl`

The oracle is the **error message**, which discriminates "refused by the
validator before dispatch" from "handed to the engine and failed there" — both
of which are merely `is_err = true` and are indistinguishable otherwise.

| run | transaction.spl | verdict |
|-----|-----------------|---------|
| RED | `origin/main` baseline | `executed=9 passed=3 failed=6 dropped=0` — all 6 injection examples fail |
| GREEN | fixed | `executed=9 passed=9 failed=0 dropped=0` |

The 3 that pass in both runs are the "validator does not refuse a plain
identifier" examples, which are guard rails against an over-tight filter and are
expected to hold on both sides. The 6 that flip are the injection examples.

The baseline was restored from `origin/main` and the fix re-installed from a
`git hash-object -w` anchored blob (`d6d45308`), verified byte-identical after
each swap.

Non-regression gate — the pre-existing `sql_transaction_spec.spl`:

| run | result |
|-----|--------|
| baseline | `executed=14 passed=6 failed=8 dropped=0` |
| fixed | `executed=14 passed=6 failed=8 dropped=0` |

Identical, so changing the emitted SQL from `SAVEPOINT sp1` to `SAVEPOINT "sp1"`
regressed nothing. Those 8 failures are pre-existing and unrelated (see below).

## Related pre-existing failures (NOT caused by this fix)

The Rust seed's in-process SQL engine does not implement `SAVEPOINT` at all, and
rejects `INSERT INTO t VALUES (1)` (no column list). That is why 8 of the 14
examples in `sql_transaction_spec.spl` fail both before and after this change,
and why the regression spec's "ordinary identifier" examples assert only that
the *validator* accepts the name rather than that the whole operation succeeds.
Seed is bootstrap-only, so this is not fixed here.

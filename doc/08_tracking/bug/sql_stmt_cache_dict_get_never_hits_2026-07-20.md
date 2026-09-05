# SQL `StatementCache.get_or_prepare` never hits cache — `Dict.get()` present-key landmine

**Date:** 2026-07-20
**Severity:** high (writes/reads silently diverge for repeated same-SQL
`exec`/`query` calls on one connection)
**Status:** open — root-cause hypothesis only, needs interpreter-side fix
(out of scope for `.spl`-source test triage per campaign guide)
**Found by:** whole-suite `test/unit/` triage campaign, `lib/database/sql`
cluster

## Symptom

`test/unit/lib/database/sql/sql_statement_spec.spl` (9/10 failures) and
`test/unit/lib/database/sql/sql_transaction_spec.spl` (8/10 failures) both
fail on the deployed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, `bin/simple test <spec>
--no-session-daemon`). Pattern:

- The FIRST `exec()`/`query()` call against a fresh `Database.memory()`
  connection with a given SQL string always succeeds and is internally
  consistent (single insert + single query on distinct SQL text: passes).
- The SECOND (or later) call using the SAME SQL text on the SAME connection
  either silently loses the write (`"inserts multiple rows with different
  parameters"`: 3x `INSERT INTO ps2 VALUES (?, ?)` with different bound
  params, then `SELECT id FROM ps2` → `expected 0 to equal 3`, i.e. 0 rows
  survive) or the whole `it` block early-returns via `?` propagation
  (`"try: early return"` — every remaining example in both specs after the
  first one, including a bare `begin()`/`execute()`/`commit()`/`query()`
  transaction sequence).

## Root-cause hypothesis

`src/lib/nogc_sync_mut/database/sql/stmt_cache.spl` (`StatementCache`,
backing every `Database.exec`/`query`/`query_one` call with `params.len() >
0` in `src/lib/nogc_sync_mut/database/sql/connection.spl:91,109,129`) caches
`PreparedStatement`s in a `Dict<text, PreparedStatement>` keyed by raw SQL
text, and looks them up with `.get()`:

```simple
# src/lib/nogc_sync_mut/database/sql/stmt_cache.spl:32-45
me get_or_prepare(conn: SqliteConnection, sql: text) -> Result<PreparedStatement, DbError>:
    match self.entries.get(sql):
        Some(cached_stmt):
            # Cache hit — move to back of LRU order
            self.hits = self.hits + 1
            self._move_to_back(sql)
            var stmt = cached_stmt
            stmt.reset_stmt()?
            return Ok(stmt)
        nil:
            pass

    # Cache miss — prepare new statement
    self.misses = self.misses + 1
    val stmt = PreparedStatement.prepare(conn, sql)?
    ...
    self.entries[sql] = stmt
    self.order.push(sql)
```

This matches the already-documented interpreter landmine in
`doc/08_tracking/bug/interp_dict_get_option_match_never_matches_2026-07-05.md`:
`Dict<K,V>.get(k)` returns the raw `V` (or `nil`) directly — it does **not**
wrap present values in `Some(..)`. A `match self.entries.get(sql): Some(x):
... nil: ...` therefore can only ever legitimately hit the `nil` arm (empty
dict / absent key); once the dict actually holds an entry for `sql`, `.get()`
returns the bare `PreparedStatement` value, which matches neither `Some(x)`
nor `nil` in the `match`.

Concretely, on the SECOND call with an already-cached SQL string:
1. First call: `sql` absent, `.get()` legitimately returns `nil`, `nil: pass`
   fires, a fresh statement is prepared and stored via `self.entries[sql] =
   stmt` (bracket-assignment works correctly, this landmine only affects
   `.get()` reads).
2. Second call, same `sql`: `self.entries.get(sql)` returns the raw
   `PreparedStatement` (present key), which doesn't match `Some(cached_stmt)`
   (not tagged) or `nil` (not nil) — the match has no matching arm. Whatever
   the interpreter does when no `match` arm binds (silently returns a default
   / bad `Result`) is what then corrupts `bind_all(params)?` /
   `stmt.execute()?` downstream, producing either quietly-lost writes (test 1)
   or `?`-propagated early return (every subsequent test, once any SQL text
   repeats within a connection — which the transaction spec's
   `begin`/`execute`/`commit`/`query` sequence also does implicitly via
   `SharedWal`/connection internals).

## Affected specs (same root, one doc)

- `test/unit/lib/database/sql/sql_statement_spec.spl` — 9 of 10 examples
  (all but `"inserts integer and text via bind"`, which only issues each SQL
  string once).
- `test/unit/lib/database/sql/sql_transaction_spec.spl` — 8 of 10 examples
  (all but the two `"error after completion"` examples that assert on an
  already-closed/completed transaction and don't depend on cache reuse).

## Scope note

This is an interpreter-semantics bug (`Dict.get()` vs `Option`-pattern
matching), not specific to the SQL module — same root class as
`interp_dict_get_option_match_never_matches_2026-07-05.md`. Filing
separately (rather than only updating that doc) because it identifies a new,
concrete, high-blast-radius production call site
(`stmt_cache.spl:32`) rather than a documentation-only landmine, and because
the downstream symptom (data loss / early return, not just a silently-skipped
branch) is more severe than the original doc's scope suggests. No `.spl`
source fix attempted here per campaign guide (interpreter-side, needs
redeploy to verify).

# Lane PURESQL — pure-Simple SQL engine correctness & coverage

Date: 2026-07-27. Status: IN PROGRESS.

## 1. Survey — which tier is live (EVIDENCE)

There is exactly **ONE** implementation. No divergence, nothing unreachable.

| Path | Lines | Role |
|---|---|---|
| `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl` | 2973 | engine |
| `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl` | 1467 | expr eval / row codec |
| `src/lib/nogc_sync_mut/database/pure_sql/database.spl` | 3 | re-export of the two above |
| `src/lib/nogc_sync_mut/database/pure_sql/__init__.spl` | 1 | `export use ...database.{PureDatabase}` |
| `src/lib/nogc_async_mut/database/pure_sql/__init__.spl` | 1 | `export use nogc_sync_mut.database.pure_sql.database.{PureDatabase}` |

**Evidence the async tier is NOT a fork:** the whole `nogc_async_mut` copy is a
single line that re-exports the `nogc_sync_mut` symbol. `ls -R` shows the async
directory contains only `__init__.spl` — no `_PureDatabase/`. So the
shadowed-tier trap does NOT apply here: `use std.database.pure_sql` resolves to
the async `__init__`, which forwards to the sync implementation. Editing the
sync copy is correct and is the only option. (Contrast with today's FAT32 case
where the sync tier held a real, unreachable 3,165-line fork.)

## 2. API surface

`PureDatabase.open(path)` / `open_deferred`, `exec_sql(sql)`,
`exec(sql, params)`, `query(sql, params)`, `query_one`, `query_value`,
`put(table, values)`, `checkpoint()`, `close()`, `changes()`,
`search(...)` / `fts5_search(...)`, `table_exists`, `last_insert_rowid`.
Statements: CREATE TABLE / CREATE [UNIQUE] INDEX / INSERT / SELECT / UPDATE /
DELETE / DROP / BEGIN / COMMIT / ROLLBACK. Expr kinds: BinaryOp, UnaryOp (NOT),
Column, Literal, Param, IsNull, IsNotNull, Between, plus LIKE / MATCH ops.

## 3. Existing spec coverage

`test/02_integration/storage/dbfs/pure_db_spec.spl`,
`pure_db_sql_extended_spec.spl`, `db_cache_invalidation_spec.spl`, plus
`test/05_perf/bench/pure_db_*`. These cover **persistence, FTS/BM25 rebuild,
and throughput** — they are round-trip and perf specs. There is essentially
**no adversarial coverage of WHERE semantics, NULL logic, or transaction
rollback**, which is where this lane focuses.

## 4. Landmine audit against the engine (static)

| Landmine | Verdict |
|---|---|
| `Some(<i64>)` 8x on JIT | **NOT PRESENT.** All 10 `Some(...)` sites wrap `DbRow`, `DbValue`, or a row struct — never a bare i64. `database/core.spl`'s bug does not replicate here. |
| `x.f += v` drops operator | **NOT PRESENT** in pure_sql (no `+=` / `-=` anywhere in either file). |
| `.to_int() ?? 0` fail-open | **3 sites.** 2 are guarded by `_is_numeric_text` (`_parse_literal` L126, `_resolve_int_literal` L225). **1 is UNGUARDED: `_deserialize_row` L100** — a corrupt/overflowing `I:` cell silently becomes 0. |
| `index_of` returns -1 not nil | 2 sites in JOIN parsing, both compared `>= 0` / guarded. OK. |
| Dict `.get()` broken natively | **Safe pattern used:** `_col_idx` does `if m.has(name): return m[name]` — index read after presence check, exactly the documented workaround. |

## 5. Correctness hypotheses (from reading; to be confirmed by test)

Ranked by blast radius. All are *silently wrong results*, the worst DB failure mode.

- **H1 — REAL vs INTEGER comparison falls back to LEXICOGRAPHIC text compare.**
  `_dbval_cmp` / `_dbval_eq` only take the numeric branch when **both** sides are
  `DbValue.Integer`. A `Real` vs `Integer` pair goes to `a.to_text() > b.to_text()`.
  So `WHERE amount > 10` with `amount = 2.5` compares `"2.5" > "10"` => TRUE.
  Expected 0 rows, actual 1 row. Also `5.0 = 5` => `"5.0" == "5"` => false.
- **H2 — NULL is two-valued, not three-valued.** `_dbval_eq` returns `true` for
  `NULL = NULL`, and `!=` is `not _dbval_eq`. SQL says both are UNKNOWN and match
  no rows. So `WHERE name = NULL` wrongly returns the NULL rows, and
  `WHERE name != 'alice'` wrongly returns NULL rows.
- **H3 — ROLLBACK does not restore the typed row cache.** `_tbl_typed` appears
  **63 times** in the engine and **0 times** in `_snapshot_tables` /
  `_restore_from_snapshot`. SELECT can serve rows straight out of
  `self._tbl_typed[ti]` (pure_database.spl L398/L418). If that cache is warm,
  a ROLLBACK restores `_tbl_data` but leaves rolled-back rows in `_tbl_typed`.
- **H4 — int fast-path range scan on a REAL column.** `_extract_int_range`
  validates only that the *literal* is numeric, never the column's storage type,
  and `_dbval_as_i64` returns **0** for `DbValue.Real`. A `BETWEEN` / two-sided
  range over a REAL column may therefore treat every value as 0.
- **H5 — arithmetic on REAL yields NULL.** `_apply_binop` `+ - *` require both
  operands `Integer`, else return `DbValue.Null`. No `/` operator at all.
- **H6 — LIKE is case-sensitive.** SQLite's LIKE is ASCII-case-insensitive by
  default. `_like_match` compares chars directly.

## 6. Specs written

- `test/02_integration/storage/dbfs/pure_db_correctness_spec.spl` — harness probe.
- `test/02_integration/storage/dbfs/pure_db_where_semantics_spec.spl` — 14 adversarial
  examples across 6 describe blocks: numeric comparison, NULL three-valued logic,
  AND/OR precedence, transaction rollback (INSERT/UPDATE/DELETE/COMMIT),
  index result-invariance + UNIQUE rejection, and parameter-binding injection safety.
  Every expectation is an absolute SQL/SQLite oracle, not a snapshot of current behaviour.

## 7. Verdicts — per describe block

Harness probe `pure_db_correctness_spec.spl`: **1 total, 1 passed** (round trip OK).

`pure_db_where_semantics_spec.spl` — BEFORE any fix (run `build/puresql_out/battery.log`):

| describe block | before |
|---|---|
| WHERE numeric comparison | 3 examples, **2 failures** |
| NULL three-valued logic | 3 examples, **2 failures** |
| boolean precedence | 2 examples, 0 failures |
| transactions | 4 examples, **1 failure** |
| indexes | 2 examples, 0 failures |
| parameter binding | 1 example, 0 failures |
| **total** | **15 total, 10 passed, 5 failed** |

Progression across fix rounds:

| run | result |
|---|---|
| `battery.log` (HEAD, no fix) | 15 total, 10 passed, **5 failed** |
| `battery2.log` (+NULL, +numeric cmp, +fast-path guard) | 15 total, 12 passed, **3 failed** |
| `battery4.log` (+REAL literal parsing) | 15 total, 14 passed, **1 failed** |
| `battery5.log` (+snapshot normalization) | **15 total, 15 passed, 0 failed** |

`pure_db_diag_spec.spl`: 4 total, 4 passed, 0 failed (`diag5.log`).
Note the final battery run also carries STRENGTHENED rollback assertions (value
checks, not just row counts) — see F6.

## 8. CONFIRMED correctness findings (measured, not inferred)

Diagnostic harness: `test/02_integration/storage/dbfs/pure_db_diag_spec.spl`
(reports counts, never indexes a possibly-empty result). Raw runs in
`build/puresql_out/diag*.log`.

### F1 — REAL literals were stored as TEXT (root cause of all REAL breakage)
`_is_numeric_text` accepts only `[-]?[0-9]+`. `_parse_literal` therefore never
matched `2.5` and fell through to `DbValue.Text("2.5")`. A column declared
`REAL` held **text**, so every comparison on it used lexicographic ordering.

Repro (`CREATE TABLE pr (id INTEGER, amount REAL)`, rows `2.5` and `30.0`):

| query | expected | actual (pre-fix) |
|---|---|---|
| `WHERE amount > 10` | 1 | **0** |
| `WHERE amount > 10.0` | 1 | **2** |
| `WHERE amount < 10` | 1 | **2** |
| `WHERE amount > 1 AND amount < 100` | 2 | **0** |

Fix: `_is_real_text` + a `DbValue.Real` branch in `_parse_literal`.

### F2 — mixed INTEGER/REAL comparison fell back to text ordering
`_dbval_cmp` / `_dbval_eq` took the numeric path only when **both** sides were
`DbValue.Integer`; anything else compared `to_text()`. So `5.0 = 5` was false
and `"2.5" > "10"` was true. Blast radius is wider than WHERE: `_dbval_cmp`
also drives **ORDER BY, MIN/MAX and BETWEEN**.
Fix: `_dbval_is_num` / `_dbval_as_f64` + a numeric branch in both functions.

### F3 — NULL used two-valued logic (FIXED, verified green)
`_dbval_eq(NULL, NULL)` returned `true` and `!=` was `not _dbval_eq`, so NULL
rows leaked into comparisons. `NOT` also mapped UNKNOWN to TRUE.

| query | expected | before | after |
|---|---|---|---|
| `WHERE name = NULL` | 0 | **1** | 0 |
| `WHERE name != 'alice'` (rows NULL,'bob') | 1 | **2** | 1 |
| `WHERE NOT (name = 'bob')` | 0 | **1** | 0 |
| `WHERE name IS NULL` | 1 | 1 | 1 |

Fix: `_is_cmp_op` guard returning `DbValue.Null` when either operand is NULL,
plus `NOT NULL -> NULL`. AND/OR deliberately left two-valued: Kleene AND/OR over
a NULL comparand already yields the correct WHERE outcome because
`_dbval_truthy(Null)` is false.

### F4 — integer fast paths silently read REAL cells as 0
`_extract_int_range` / `_extract_single_int_bound` scans compare with
`_dbval_as_i64`, which returns **0** for a `Real` (or `Text`) cell, and they
validated only that the *literal* was numeric — never the column's storage type.
Fix: `_typed_col_int_scannable` guard (INTEGER-or-NULL columns only) on both
fast paths, plus an explicit NULL skip inside the scans.

### F5 — ROLLBACK corrupted the per-table parallel arrays
`_restore_from_snapshot` handled only 20 of the **27** per-table parallel arrays:
- **pushed without resetting** (grew to 2N on every ROLLBACK):
  `_tbl_all_visible`, `_tbl_pk_dirty`, `_tbl_mvcc_stale`, `_tbl_pk_name`
- **ignored entirely** (left stale at N, or empty):
  `_tbl_typed`, `_tbl_pk_col`, `_tbl_pk_map`, `_tbl_fts_next_doc_id`,
  `_tbl_fts_doc_ids`, `_tbl_dirty`

Measured symptom: after `BEGIN; UPDATE ...; ROLLBACK`, a full scan
`SELECT * FROM t` returned the right row count, but the **PK/indexed** read
`SELECT * FROM t WHERE id = 1` returned **0 rows** — a rolled-back UPDATE made
the row unreachable by key. `_tbl_typed` is read directly at 20+ sites and is
never rebuilt lazily, so leaving it stale/empty is unsound.
Fix: reset all remaining arrays, snapshot+restore PK metadata via two new
`_snap_tbl_pk_col` / `_snap_tbl_pk_name` fields, mark `_tbl_pk_dirty = true`
(pk_map was cleared, so it must be rebuilt), and repopulate `_tbl_typed` in
lockstep with the MVCC re-insert using extract-mutate-write-back.

### F6 — ROLLBACK restored every row as a single NULL cell (worst finding)
The MVCC tuple `data` field has **two incompatible meanings**. The typed fast
INSERT path stores a positional handle — `tbl.insert(tid, "{tuple_pos}")`
(pure_database.spl L2198/L2305/L2315) — that indexes `_tbl_typed`, while the
slow path stores an actual `_serialize_row(values)` (L573). `_snapshot_tables`
captured `tbl.scan(snap)` verbatim, so for any fast-path table the snapshot held
`"0"`, `"1"`, … Restoring then ran `_deserialize_row("0")`, which splits on `\t`
into one part, matches no `I:`/`T:`/`R:` prefix, and falls to the `else` branch
returning `DbValue.Null`.

Measured after `BEGIN; UPDATE; ROLLBACK` on `rv (id, n)` holding `(1, 10)`:

| probe | expected | actual (pre-fix) |
|---|---|---|
| row count | 1 | 1 (looked fine) |
| `columns.len()` | 2 | 2 (looked fine) |
| `values.len()` | 2 | **1** |
| `values[0]` | 1 | **NULL** |
| `SELECT ... WHERE id = 1` | 1 | **0** |

So **every ROLLBACK silently destroyed the contents of every row it restored**,
while preserving the row count. The pre-existing rollback specs asserted only
`rows.len()`, which is exactly why this survived: the count was always right.
Control: a table never touched by a transaction kept `nvals=2`.

Fix: normalize in `_snapshot_tables` — when the scanned `data` is a bare numeric
handle, resolve it through `_tbl_typed[ti][pos]` and store `_serialize_row(...)`,
so the snapshot has exactly one representation. Rollback specs were then
strengthened to assert cell VALUES, not just row counts.

## 9. Verified-good behaviour (no action)

- **AND/OR precedence is correct**: `a=1 OR b=1 AND id=3` parses as
  `a=1 OR (b=1 AND id=3)`, and explicit parentheses are honoured.
- **Indexes are result-invariant**: identical rows before and after
  `CREATE INDEX`; a `UNIQUE` index rejects the duplicate INSERT and no row lands.
- **Parameter binding is safe**: `query("... WHERE name = ?", [payload])` with
  `alice' OR '1'='1` returns 0 rows and leaves the table intact. Placeholders
  resolve to `DbValue` via `_expr_to_dbvalue`, never by string splicing.
- ROLLBACK of INSERT and of DELETE, and COMMIT durability across reopen, all pass.

## 10. Filed, not fixed (out of scope for this lane)

- `IN (...)` and `BETWEEN` call `_dbval_eq` / `_dbval_cmp` directly, bypassing
  the `_apply_binop` NULL guard, so they remain two-valued for NULL operands.
- `_apply_binop` `+ - *` return `DbValue.Null` for non-Integer operands, so REAL
  arithmetic yields NULL; there is no `/` operator at all.
- `LIKE` is case-sensitive; SQLite's default LIKE is ASCII case-insensitive.
- `_deserialize_row` L100 uses an unguarded `.to_int() ?? 0`, so a corrupt or
  overflowing `I:` cell silently reads as 0 (the other two `to_int` sites are
  guarded by `_is_numeric_text`).
- `_is_real_text` does not accept exponent form (`1e5`); deliberately narrow so
  nothing non-numeric is reclassified away from TEXT.

## 8. Notes for other lanes

- Lane SQLVFS: the `CREATE INDEX IF NOT EXISTS` parse bug is in the shared
  `sql_parse`, not in these two files.
- The `database:` row in `doc/08_tracking/os/production_status.sdn` is shared
  with lanes SQLVFS and DBDUR — this lane appends a short clause only.

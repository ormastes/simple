# SStack State: db-fts-engine

## User Request
> impl all feature to embedded db(sqlite) research more and add to embedded sql and share it with full db. research and plan and impl. Build classical IR search engine (FTS5/BM25 + trigram + fuzzy) for Simple DB — not vector/semantic search. Share between embedded DB (pure_sql) and full engine (dbfs_engine).

## Task Type
feature

## Refined Goal
> Build a pure-Simple full-text search (FTS) engine and complete missing embedded DB features. The FTS engine implements classical IR: inverted index with BM25 ranking, trigram substring matching, and Levenshtein fuzzy search. Integrate into PureDatabase (embedded layer at `database/pure_sql/`) and expose shared modules for the full DB engine (`db/dbfs_engine/`). Also add critical missing SQL features (aggregate functions, DROP TABLE, LIKE, DISTINCT) to PureDatabase to approach SQLite feature parity.

## Acceptance Criteria
- [ ] AC-1: Text tokenizer — normalize text (lowercase, strip punctuation), split into tokens, stop-word filtering
- [ ] AC-2: Inverted index — term→posting-list (doc_id + term frequency + positions), insert/delete/update
- [ ] AC-3: BM25 ranking — score documents using BM25(k1=1.2, b=0.75), return ranked results with scores
- [ ] AC-4: Trigram index — generate 3-char substrings for partial/substring matching
- [ ] AC-5: Fuzzy search — Levenshtein distance, configurable edit-distance threshold
- [ ] AC-6: FTS query API — unified `fts_search(query)` combining keyword + trigram + fuzzy, returns ranked results
- [ ] AC-7: PureDatabase FTS integration — auto-index on INSERT/UPDATE/DELETE, MATCH syntax in WHERE
- [ ] AC-8: Missing SQL features in PureDatabase — COUNT/SUM/AVG/MIN/MAX aggregates, DROP TABLE, LIKE operator, DISTINCT
- [ ] AC-9: Shared module structure — FTS modules under `db/dbfs_engine/fts/` importable by both embedded and full DB
- [ ] AC-10: Test specs — tokenizer, inverted index, BM25, trigram, fuzzy, integrated FTS search, aggregate functions (all green)
- [ ] AC-11: JOIN support in PureDatabase — INNER JOIN with ON condition, cross-table queries

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-24
- [x] 2-research (Analyst) — 2026-05-24
- [x] 3-arch (Architect) — 2026-05-24
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** Build pure-Simple FTS engine (inverted index + BM25 + trigram + fuzzy) and complete missing PureDatabase SQL features. Classical IR approach, not vector/semantic search.

**Key context:**
- PureDatabase MVP exists at `database/pure_sql/database.spl` — 12/12 tests green (CREATE TABLE, INSERT, SELECT, UPDATE, DELETE with WHERE, LIMIT/OFFSET, column projection)
- SQL parser at `db/dbfs_engine/sql_parser.spl` — 1217 lines, supports full SQL surface
- MVCC at `db/dbfs_engine/mvcc.spl` — PostgreSQL-style visibility
- CRC32 checksums in core.spl + wal.spl
- User explicitly wants classical IR (FTS5/BM25/trigram/fuzzy), NOT vector DB or embeddings
- User wants hybrid future option: FTS + AST graph + optional embeddings

**Acceptance criteria:** 10 ACs covering tokenizer, inverted index, BM25, trigram, fuzzy, FTS API, PureDatabase integration, missing SQL features, shared module structure, and test specs.

### 2-research

**Headline finding:** The SQL parser (1217 lines) already parses most SQL features needed. The gap is in the **executor** (`PureDatabase._do_select`) which ignores parsed JOIN, GROUP BY, HAVING, ORDER BY, and DISTINCT AST nodes.

#### Current Capability Inventory

**PureDatabase (`database/pure_sql/database.spl`, 498 lines):**
- Working: CREATE TABLE (IF NOT EXISTS), INSERT, SELECT (*, column projection), UPDATE, DELETE, WHERE (=, !=, <, >, <=, >=, AND, OR, NOT), LIMIT/OFFSET, parameterized queries (?), close/open, table_exists
- 12/12 test specs green (`test/dbfs/pure_db_spec.spl`)
- Storage: MVCC-backed (`MvccTable.scan(snapshot) -> [text]`), serialized rows (tab-delimited, typed cells)
- Missing in executor: JOIN, GROUP BY, HAVING, ORDER BY, DISTINCT, aggregates, DROP TABLE, LIKE eval, FTS/MATCH

**SQL Parser (`db/dbfs_engine/sql_parser.spl`, 1217 lines):**
- **Parses (AST built):** SELECT, INSERT, UPDATE, DELETE, CREATE TABLE
- **Parses correctly:** JOIN (Inner/Left/Right/Cross/Outer/Full via `JoinKind` enum + `SqlJoin` struct), GROUP BY (`[SqlExpr]`), HAVING (`SqlExpr?`), ORDER BY (`[SqlOrderBy]`), DISTINCT (bool), BETWEEN, IN, LIKE (as `BinaryOp("LIKE")`), IS NULL / IS NOT NULL, CASE/WHEN, function calls (`SqlExprKind.FunctionCall`), Subquery (`SqlExprKind.Subquery`), aliased columns (AS), table aliases
- **NOT parsed:** DROP TABLE (token exists but no `SqlStmtKind.Drop`, no `_parse_drop`, not in `parse()` dispatch), ALTER TABLE (token exists, no parse path), UNION (no token/parse path)
- **MATCH (for FTS):** No token. Recommend function-call route (`WHERE fts_match(col, 'query')`) — parser already handles `FunctionCall` expressions, no parser changes needed.

**MVCC (`db/dbfs_engine/mvcc.spl`):**
- `MvccTable`: insert(txn_id, data), delete_matching(txn_id, data), scan(snapshot) -> [text], count_visible(snapshot)
- `MvccTxnManager`: begin, commit, abort, snapshot
- No row-ID stability — rows identified by serialized data string, not integer ID. Inverted-index posting lists must use data hash or doc-id map.

**Existing FTS code (`database/fts.spl` — both sync and async copies):**
- Trigram-only: `trigram_extract`, `fts_build`, `fts_search`, `fts_update`
- Bound to `database.core.SdnTable` (old API), NOT to `MvccTable`/`PureDatabase`
- No BM25, no inverted index (term→postings), no tokenizer, no fuzzy/Levenshtein
- Insertion-sort ranking — O(n^2), not suitable for large result sets
- **Decision for arch:** reuse/extend existing fts.spl vs. rebuild under `db/dbfs_engine/fts/` per AC-9

**Existing test specs:** `test/dbfs/` has 35+ spec files (btree, WAL, checkpoint, pager, MVCC visibility, SQL parser, recovery, etc.). Pure DB has `pure_db_spec.spl`.

#### Parser vs. Executor Gap Matrix

| Feature | Parser | Executor | AC |
|---------|--------|----------|----|
| JOIN (INNER/LEFT/RIGHT/CROSS) | Yes (`SqlJoin`, `JoinKind`) | No | AC-11 |
| GROUP BY | Yes (`group_by: [SqlExpr]`) | No | AC-8 |
| HAVING | Yes (`having: SqlExpr?`) | No | AC-8 |
| ORDER BY | Yes (`order_by: [SqlOrderBy]`) | No | AC-8 |
| DISTINCT | Yes (`distinct: bool`) | No | AC-8 |
| Aggregate fns (COUNT/SUM/AVG/MIN/MAX) | Yes (via `FunctionCall`) | No | AC-8 |
| LIKE | Yes (`BinaryOp("LIKE")`) | No (`_apply_binop` doesn't handle "LIKE") | AC-8 |
| DROP TABLE | Token only — no parse/dispatch | No | AC-8 |
| BETWEEN | Yes | Needs `_eval_expr` case | — |
| IN | Yes | Needs `_eval_expr` case | — |
| MATCH/FTS | No (use FunctionCall route) | No | AC-7 |

#### FTS Implementation Plan (per component)

**Tokenizer (AC-1):**
- Lowercase, strip punctuation (ASCII for MVP), split on whitespace
- Stop-word list (~30 English words: "the", "is", "at", etc.)
- Pure Simple: `text.to_lower()`, iterate chars, filter
- No extern needed

**Inverted Index (AC-2):**
- `Dict<text, [PostingEntry]>` where `PostingEntry` = `{doc_id: i64, tf: i64, positions: [i64]}`
- Document registry: `Dict<i64, i64>` for doc_id → doc_length
- Insert/delete/update maintain postings
- No extern needed — Dict + array are sufficient

**BM25 Ranking (AC-3):**
- Formula: `score = IDF * (tf * (k1+1)) / (tf + k1 * (1 - b + b * dl/avgdl))`
- IDF = `ln((N - df + 0.5) / (df + 0.5) + 1)` where N=total docs, df=docs containing term
- Parameters: k1=1.2, b=0.75 (configurable)
- Requires: total doc count, avg doc length, per-doc length — stored in index metadata
- Pure arithmetic — no extern needed

**Trigram Index (AC-4):**
- Reuse logic from existing `fts.spl`: `trigram_extract(s)` generates 3-char substrings
- `Dict<text, [i64]>` mapping trigram → doc_ids
- For substring LIKE '%pattern%' acceleration

**Fuzzy/Levenshtein (AC-5):**
- Classic DP matrix: `var dp: [[i64]]` of size (m+1)x(n+1)
- Threshold: default max_distance=2 (configurable)
- Applied to each unique term in index vocabulary — filter candidates by first-char or trigram overlap to avoid full scan
- Pure Simple — no extern needed

**FTS Query API (AC-6):**
- `fts_search(query: text) -> [FtsResult]` combining:
  1. Tokenize query → BM25 keyword search (primary)
  2. Trigram match for substring/partial (secondary)
  3. Fuzzy expansion for typo tolerance (tertiary)
- Merge + re-rank results, apply limit

**PureDatabase Integration (AC-7):**
- Prefer function-call syntax: `WHERE fts_match(column, 'query')` — no parser changes
- Auto-index: hook `_do_insert`, `_do_update`, `_do_delete` to update FTS index
- PureDatabase holds `Dict<text, FtsEngine>` keyed by "table.column"
- New method: `create_fts_index(table, column)` to enable FTS on a column

#### JOIN Implementation Approach (AC-11)

- Parser already produces `SqlSelect.joins: [SqlJoin]` with `JoinKind` + `on_expr`
- Executor needs nested-loop join in `_do_select`:
  1. Scan base table (from_table) rows via MVCC
  2. For each join: scan joined table, evaluate `on_expr` for each row pair
  3. LEFT JOIN: emit NULL-padded row when no match found
  4. Column namespace: prefix with table name or alias for disambiguation
- Performance: O(n*m) nested-loop is acceptable for embedded use; no hash join needed for MVP

#### Aggregate / GROUP BY Implementation (AC-8)

- `_do_select` needs second pass after WHERE filtering:
  1. If `group_by` non-empty: bucket rows by group-key values into `Dict<text, [[DbValue]]>`
  2. For each bucket: evaluate aggregate functions (COUNT, SUM, AVG, MIN, MAX) via `SqlExprKind.FunctionCall` dispatch
  3. If no GROUP BY but aggregates present: treat entire result as one group
- ORDER BY: sort result rows by `order_by` expressions using `_dbval_cmp`
- DISTINCT: deduplicate via serialized-row set (`Dict<text, bool>`)
- LIKE: add `"LIKE"` case to `_apply_binop` — simple `%`/`_` pattern matching on text

#### DROP TABLE

- Add `SqlStmtKind.Drop` to enum
- Add `drop_table: text?` field to `SqlStatement`
- Add `_parse_drop()` in parser, route from `parse()` dispatch
- Add `_do_drop()` in PureDatabase: remove from `_tbl_names`, `_tbl_cols`, `_tbl_data`

#### Risks and Language Limitations

- **No row-ID stability in MVCC:** `MvccTable.scan()` returns `[text]`, no stable integer IDs. FTS posting lists need a doc-ID mapping layer (auto-increment counter per table).
- **Insertion-sort is O(n^2):** Existing FTS and future BM25 ranking need better sort for large result sets. Simple has no built-in sort — implement merge-sort helper.
- **ASCII-only tokenizer for MVP:** Unicode word-boundary detection is complex. Flag as follow-up.
- **Interpreter perf:** Large inverted indexes (>10K docs) may hit interpreter bottlenecks (Value::Str copies, expr cascade). Compiled mode recommended for production use.
- **2D array for Levenshtein:** `[[i64]]` allocation per fuzzy call — acceptable for small vocab, may need pooling at scale.
- **No UNION/ALTER/subquery execution** in scope — parser has tokens/AST nodes but execution is out of scope for this feature.

#### Module Structure Recommendation (for arch)

```
src/lib/nogc_sync_mut/db/dbfs_engine/fts/
  tokenizer.spl      — AC-1
  inverted_index.spl  — AC-2
  bm25.spl            — AC-3
  trigram.spl          — AC-4 (port from existing fts.spl)
  fuzzy.spl            — AC-5
  engine.spl           — AC-6 (unified API)
```
PureDatabase imports from `db.dbfs_engine.fts.engine` — shared with full DB engine per AC-9.

### 3-arch
**Module Layout (confirmed from research):**
```
db/dbfs_engine/fts/
  tokenizer.spl        — FtsToken, fts_tokenize(), fts_tokenize_raw()
  inverted_index.spl   — FtsInvertedIndex, FtsPosting
  bm25.spl             — FtsSearchResult, fts_bm25_score(), fts_bm25_search()
  trigram.spl           — FtsTrigramIndex, fts_generate_trigrams()
  fuzzy.spl             — fts_levenshtein(), fts_fuzzy_match()
  search.spl            — FtsEngine (unified API)
  __init__.spl          — re-exports
```

**PureDatabase enhancements (in database.spl):**
- `_apply_binop`: add LIKE → `_like_match()` pattern matcher
- `_do_select`: add DISTINCT dedup, aggregate detection + GROUP BY grouping, JOIN execution, ORDER BY sorting
- `exec`: add DROP TABLE (manual parse since parser lacks DropTable variant)
- New helpers: `_do_join()`, `_group_and_aggregate()`, `_sort_rows()`, `_like_match()`

**Key architectural decisions:**
1. FTS uses function-call syntax (`fts_match(col, query)`) — no parser changes needed
2. New FTS modules at `db/dbfs_engine/fts/` — independent of legacy `database/fts.spl`
3. BM25 scoring uses integer approximation (×1000) — avoids f64 interpreter issues
4. Doc-ID mapping: auto-increment counter per table in FtsEngine
5. No parser modification for DROP TABLE — manual string parse in PureDatabase.exec()

Phase 3 done — architecture validated against research findings.

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>

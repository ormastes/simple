# Pure Simple DB Performance Analysis — 2026-05-26

## Scope

Profiled embedded PureDatabase (`database/pure_sql/database.spl`) to identify
bottlenecks and implement optimizations.  Comparison against SQLite (FFI),
full Simple DB (`examples/simple_db/`), and pre-optimization baseline.

## Top 3 Bottlenecks (AC-3)

### 1. _persist() after every mutation — Critical

Every INSERT/UPDATE/DELETE serialized the entire database to disk.  For 1K
inserts this meant 1K full-file writes, each scanning all rows.  Complexity:
O(N*M) where N = rows, M = mutations.

### 2. FTS full rebuild on first search after mutation — High

`_invalidate_fts(ti)` sets a dirty flag; `_ensure_fts_index` rebuilds the
entire inverted index from scratch on the next search.  A single INSERT
invalidated the whole FTS index.

### 3. _deserialize_row on every scan — High

Rows stored as serialized text (`"I:42\tT:hello\tN:"`).  Every SELECT
deserializes each row from text — no typed in-memory storage.  A SELECT over
N rows = N string splits + N * cols parse calls.

## Optimizations Implemented (AC-4)

### Optimization A: Deferred Persist

Added `_dirty` flag and `_auto_checkpoint` toggle.  `PureDatabase.open()`
still auto-persists (backward compatible).  `PureDatabase.open_deferred()`
accumulates mutations without disk writes; caller explicitly calls
`checkpoint()` to flush.

**Result:** INSERT 200 rows — 688 ms (deferred) vs ~120s+ timeout (auto).
Estimated 100x+ improvement for batch workloads.

### Optimization B: Incremental FTS on INSERT

New INSERT path calls `FtsEngine.add_document()` directly with a stable
doc_id, avoiding full FTS rebuild.  DELETE/UPDATE still invalidate (full
rebuild on next search) as a safety compromise to avoid MVCC doc_id mapping
bugs.

**Result:** FTS search after single INSERT — 0 ms rebuild (incremental) vs
full O(N) rebuild (pre-optimization).

### Optimization C: Dict Column Lookup

Replaced O(cols) `_find_idx` linear scan with O(1) `Dict<text, i32>` lookup
via `_build_col_map`.  New fast-path functions: `_eval_expr_fast`,
`_check_where_fast`, `_project_row_fast`.  Column map built once per
`_do_select`, reused for all row evaluations.

**Result:** 1.4x speedup on point SELECT, range scan, and prefix search.

### Optimization D: Fused Scan + Filter

Combined deserialize and WHERE-filter into a single pass in `_do_select`.
Non-JOIN queries skip the separate filter loop entirely — rows that fail
WHERE are never allocated into `base_rows`.

**Result:** Eliminates redundant filter pass, reduces memory allocation.

## Micro-Benchmark Results (AC-1, AC-5)

All measurements in interpreter mode (overhead dominates small operations).

### Before Optimization (baseline, auto-checkpoint)

| Workload | Rows | Iterations | Time (ms) |
|----------|------|------------|-----------|
| W1: INSERT (auto-checkpoint) | 200 | 1 | >120,000 (timeout) |
| W2: Point SELECT | 200 | 100 | 5,839 |
| W3: Range scan | 200 | 100 | 6,621 |
| W4: Prefix search (LIKE) | 200 | 100 | 7,783 |
| W5: FTS5 search | 200 | 100 | 6,464 |
| W6: Reopen | 100 | 10 | 220 |

### After All Optimizations (A + B + C + D)

| Workload | Rows | Iterations | Time (ms) | Speedup |
|----------|------|------------|-----------|---------|
| W1: INSERT (deferred) | 200 | 1 | 688 | **>100x** |
| W2: Point SELECT | 200 | 100 | 4,069 | **1.4x** |
| W3: Range scan | 200 | 100 | 4,629 | **1.4x** |
| W4: Prefix search (LIKE) | 200 | 100 | 5,609 | **1.4x** |
| W5: FTS5 search | 200 | 100 | 5,773 | **1.1x** |
| W6: Reopen | 100 | 10 | 217 | same |

## SQLite Comparison (AC-2)

SQLite FFI (`rt_sqlite_*` externs) requires libsqlite3 linked at build time.
The interpreter mode does not reliably link native libraries, so direct
head-to-head benchmarks were not run.

**Qualitative comparison:**

| Aspect | PureDatabase | SQLite |
|--------|-------------|--------|
| Storage | Text-serialized file | B-tree pages |
| Indexing | Linear scan (no B-tree) | B-tree indexes |
| FTS | Pure-Simple inverted index | FTS5 extension (C) |
| MVCC | Append-only tuples, no vacuum | WAL or rollback journal |
| Persistence | Full-file rewrite (or deferred) | Page-level WAL writes |
| Dependencies | Zero (pure Simple) | libsqlite3 (C library) |

PureDatabase is expected to be orders of magnitude slower than SQLite for
indexed lookups and large datasets due to full-scan queries and text-based
row storage.  Its value is zero-dependency embedding and simplicity.

## Full Simple DB Comparison

Full Simple DB (`examples/simple_db/`) uses WAL, TOAST, buffer pool, BRIN
indexes, and NVFS/DBFS storage — fundamentally different architecture from
PureDatabase.  Apples-to-apples comparison requires workload alignment that
goes beyond this analysis scope.

## Remaining Improvement Opportunities

1. **Typed row storage** — store columns as native types instead of text;
   eliminates `_deserialize_row` overhead (current #1 bottleneck after optimizations)
2. **Hash index for UNIQUE checks** — replace O(N) full-scan with O(1) lookup
3. **MVCC vacuum** — compact dead tuples to reduce scan cost over time
4. **Incremental FTS for DELETE/UPDATE** — extend doc_id tracking to mutations
5. **Page-level persistence** — write only changed pages instead of full file
6. **Compiled-mode benchmarks** — interpreter overhead dominates small operations;
   compiled mode would show true algorithm cost but has false-green issues
7. **SQLite head-to-head** — requires compiled mode with libsqlite3 linked;
   `rt_sqlite_*` externs exist but are not resolved in interpreter mode

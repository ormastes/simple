# PureDatabase.fts5_search over-matches after mixed DELETE+INSERT (incremental FTS index)

**Date:** 2026-07-20
**Status:** OPEN
**Area:** `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl` (`search`,
`_ensure_fts_index` / `_ensure_fts_index_typed`, `_fts_valid` incremental-index path)

## Symptom

After a sequence of `INSERT` (10 rows) → `fts5_search` (warms/builds the FTS
index) → `DELETE` (5 rows) → `INSERT` (5 new rows) → `fts5_search`, a query for
a token unique to exactly one surviving row (`"fresh_12"`, present only in the
row with `id=12`) matches **all 5** newly-inserted `fresh_*` rows instead of
just the 1 row that actually contains that token.

```
all_common=10        # correct: "common_word" is in every row
fresh_12 matches=5    # WRONG: should be 1 (only id=12's body contains "fresh_12")
expected 5 to equal 1
```

Two adjacent, simpler tests in the same file **pass**: a pure INSERT (no
DELETE) FTS-findability check, and a pure DELETE FTS-removal check. Only the
mixed DELETE-then-INSERT sequence over-matches, pointing at the incremental
index-maintenance path (`_fts_valid` / `_ensure_fts_index*`) rather than the
tokenizer or the BM25 scorer in general.

## Minimal repro

```simple
use std.spec
use std.database.pure_sql.database.{PureDatabase}

describe "fts incremental mix repro":
    it "mixed insert+delete fts search stays exact":
        var db = PureDatabase.memory_deferred().unwrap()
        db.exec_sql("CREATE TABLE fts_m (id INTEGER, body TEXT)").unwrap()
        var i = 0
        while i < 10:
            db.exec_sql("INSERT INTO fts_m (id, body) VALUES (" + i.to_text() + ", 'term_" + i.to_text() + " common_word document')").unwrap()
            i = i + 1
        db.fts5_search("fts_m", ["body"], "common_word", 20).unwrap()  # warm index
        var j = 0
        while j < 5:
            db.exec_sql("DELETE FROM fts_m WHERE id = " + j.to_text()).unwrap()
            j = j + 1
        var k = 10
        while k < 15:
            db.exec_sql("INSERT INTO fts_m (id, body) VALUES (" + k.to_text() + ", 'fresh_" + k.to_text() + " common_word document')").unwrap()
            k = k + 1
        val fresh = db.fts5_search("fts_m", ["body"], "fresh_12", 5).unwrap()
        expect(fresh.len()).to_equal(1)   # actual: 5
```

Reproduces in-memory (`PureDatabase.memory_deferred()`), so it is not
file-backend-specific. Saved at
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/3a5335e6-6c02-459b-9ac1-fa39d352df7e/scratchpad/repro_fts_mix_spec.spl`
for reference (scratch path, not part of the tracked test suite).

## Failing command

```
BIN=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
SIMPLE_RUST_SEED_WARNING=0 timeout 90 "$BIN" test test/05_perf/bench/pure_db_optimization_spec.spl --no-session-daemon
```

Failing example: `describe "..." / it "mixed INSERT+DELETE maintains FTS
correctness"` (line ~175-215 of
`test/05_perf/bench/pure_db_optimization_spec.spl`), specifically the
`expect(fresh.len()).to_equal(1)` assertion on line 213.

## Root-cause hypothesis

`search()` (pure_database.spl:1371) has a cached/incremental fast path guarded
by `self._fts_valid[ti]`: if the cached index is still marked valid and the
column set matches, it reuses `self._fts_indexes[ti]` / `self._fts_rows[ti]`
without a full rebuild (`_ensure_fts_index` / `_ensure_fts_index_typed` are the
rebuild path, only invoked when `not fts_cached`). The two adjacent passing
tests each perform a *single* kind of mutation (insert-only, delete-only)
after the initial warm-up query, but the failing test performs a DELETE
**followed by** an INSERT before the next search. The most likely defect is in
whatever incremental-delta code path updates `_fts_indexes[ti]` /
`_fts_rows[ti]` on DELETE+INSERT without a full rebuild: either
  - deleted-row postings are not fully evicted from the FTS posting lists
    before new rows are appended (so old `doc_id`s still contribute matches),
    and/or
  - newly-inserted rows are appended at row-index slots that collide with (or
    alias) the just-deleted rows' old slots, so the query "fresh_12" ends up
    scoring against stale postings that still reference the vacated slot
    range as if they all matched the new token.

Either way the net effect is that a token unique to one new row scores as a
match against all 5 newly-inserted rows, which is consistent with a
delta-applied-per-batch bug (touches all rows added since the last full
rebuild) rather than a per-document tokenization bug.

## Not attempted

Per triage scope, no fix was made to `pure_database.spl` — this doc only
records the defect. The two simpler "insert-only" and "delete-only" incremental
tests in the same spec file continue to pass and were left untouched.

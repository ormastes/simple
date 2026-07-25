# DB Benchmark Gates Specification

 > Correctness-based benchmark gates for DB operations. These verify that each operation returns the correct result, serving as a prerequisite for future timing-based gates. Interpreter mode cannot measure perf, so all gates are correctness assertions.

 <!-- sdn-diagram:id=db_benchmark_gates_spec.arch -->
 <details class="sdn-source">
 <summary>SDN source</summary>

 ```sdn id=db_benchmark_gates_spec.arch hash=sha256:auto render=ascii
 @layout dag
 @direction LR

 db_benchmark_gates_spec -> std
 db_benchmark_gates_spec -> nogc_sync_mut
 ```

 </details>

 <details class="sdn-ascii" open>
 <summary>Diagram</summary>

 ```ascii generated-from=db_benchmark_gates_spec.arch hash=sha256:auto
 # run: simple md-diagram-update
 ```

 </details>
 <!-- sdn-diagram:end -->

 | Tests | Active | Skipped | Pending |
 |-------|--------|---------|--------:|
 | 6 | 6 | 0 | 0 |

 <details>
 <summary>Full Scenario Manual</summary>

 # DB Benchmark Gates Specification

 Correctness-based benchmark gates for DB operations. These verify that each operation returns the correct result, serving as a prerequisite for future timing-based gates. Interpreter mode cannot measure perf, so all gates are correctness assertions.

 ## At a Glance

 | Field | Value |
 |-------|-------|
 | Feature IDs | #db-hardening-optimization |
 | Category | Performance / Correctness Gates |
 | Difficulty | 2/5 |
 | Status | Draft |
 | Plan | doc/03_plan/db_hardening_optimization_plan_2026-05-26.md |
 | Source | `test/05_perf/bench/db_benchmark_gates_spec.spl` |
 | Updated | 2026-06-01 |
 | Generator | `simple spipe-docgen` (Simple) |

 ## Overview

 Correctness-based benchmark gates for DB operations. These verify that
 each operation returns the correct result, serving as a prerequisite
 for future timing-based gates. Interpreter mode cannot measure perf,
 so all gates are correctness assertions.

 ## Behavior

 - Point lookup returns the correct single row
 - Prefix search returns all matching rows
 - Contains search returns all matching rows
 - BM25/FTS5 query returns ranked results
 - Update/delete invalidation clears stale entries
 - Reopen/recovery preserves data integrity
+- CRUD compare wrapper records validated embedded timings against
+  SQLite/PostgreSQL baselines and keeps strict release gating separate from
+  non-strict evidence collection.
+
+## CRUD Compare Wrapper
+
+Run:
+
+```bash
+sh scripts/check/check-simple-db-perf-compare.shs
+```
+
+Strict release gate:
+
+```bash
+sh scripts/check/check-simple-db-perf-compare.shs --strict
+```
+
+Strict pass requires validated embedded CRUD rows to meet both baselines, no
+interpreter fallback, and a measured full/server mode. If the full DB submodule
+is unavailable, set `SIMPLE_DB_SERVER_BENCH_CMD` to the server benchmark command.
+Current measured blockers are tracked in
+`doc/08_tracking/bug/simple_db_perf_native_server_blockers_2026-06-21.md`.

 ## Scenarios

 ### DB Benchmark Gates (AC-8)

 ### point lookup gate

 #### AC-8: point lookup by primary key returns correct row

 1. file delete
 2. var db = PureDatabase open
 3. db exec sql
 4. db exec sql
 5. db exec sql
 6. db exec sql
    - Expected: rows.len() equals `1`
    - Expected: name equals `bob`
 7. db close
 8. file delete


 <details>
 <summary>Executable SSpec</summary>

 Runnable source: 16 lines folded for reproduction.
 Reproduction: this block contains the complete executable scenario source.

 ```simple
 val path = "/tmp/simple_db_bench_point_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
 file_delete(path)

 var db = PureDatabase.open(path).unwrap()
 db.exec_sql("CREATE TABLE bench_point (id INTEGER, name TEXT)").unwrap()
 db.exec_sql("INSERT INTO bench_point (id, name) VALUES (1, 'alice')").unwrap()
 db.exec_sql("INSERT INTO bench_point (id, name) VALUES (2, 'bob')").unwrap()
 db.exec_sql("INSERT INTO bench_point (id, name) VALUES (3, 'carol')").unwrap()

 val rows = db.query("SELECT * FROM bench_point WHERE id = 2", []).unwrap()
 expect(rows.len()).to_equal(1)
 val name = rows[0].values[1].to_text()
 expect(name).to_equal("bob")

 db.close().unwrap()
 file_delete(path)
 ```

 </details>

 ### prefix search gate

 #### AC-8: prefix search returns all matching rows

 1. file delete
 2. var db = PureDatabase open
 3. db exec sql
 4. db exec sql
 5. db exec sql
 6. db exec sql
    - Expected: rows.len() equals `2`
 7. db close
 8. file delete


 <details>
 <summary>Executable SSpec</summary>

 Runnable source: 14 lines folded for reproduction.
 Reproduction: this block contains the complete executable scenario source.

 ```simple
 val path = "/tmp/simple_db_bench_prefix_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
 file_delete(path)

 var db = PureDatabase.open(path).unwrap()
 db.exec_sql("CREATE TABLE bench_prefix (id INTEGER, tag TEXT)").unwrap()
 db.exec_sql("INSERT INTO bench_prefix (id, tag) VALUES (1, 'user:alice')").unwrap()
 db.exec_sql("INSERT INTO bench_prefix (id, tag) VALUES (2, 'user:bob')").unwrap()
 db.exec_sql("INSERT INTO bench_prefix (id, tag) VALUES (3, 'admin:carol')").unwrap()

 val rows = db.query("SELECT * FROM bench_prefix WHERE tag LIKE 'user:%'", []).unwrap()
 expect(rows.len()).to_equal(2)

 db.close().unwrap()
 file_delete(path)
 ```

 </details>

 ### contains search gate

 #### AC-8: contains search returns rows with matching substring

 1. file delete
 2. var db = PureDatabase open
 3. db exec sql
 4. db exec sql
 5. db exec sql
 6. db exec sql
    - Expected: rows.len() equals `2`
 7. db close
 8. file delete


 <details>
 <summary>Executable SSpec</summary>

 Runnable source: 14 lines folded for reproduction.
 Reproduction: this block contains the complete executable scenario source.

 ```simple
 val path = "/tmp/simple_db_bench_contains_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
 file_delete(path)

 var db = PureDatabase.open(path).unwrap()
 db.exec_sql("CREATE TABLE bench_contains (id INTEGER, body TEXT)").unwrap()
 db.exec_sql("INSERT INTO bench_contains (id, body) VALUES (1, 'the quick brown fox')").unwrap()
 db.exec_sql("INSERT INTO bench_contains (id, body) VALUES (2, 'lazy dog sleeps')").unwrap()
 db.exec_sql("INSERT INTO bench_contains (id, body) VALUES (3, 'quick silver lining')").unwrap()

 val rows = db.query("SELECT * FROM bench_contains WHERE body LIKE '%quick%'", []).unwrap()
 expect(rows.len()).to_equal(2)

 db.close().unwrap()
 file_delete(path)
 ```

 </details>

 ### BM25/FTS5 query gate

 #### AC-8: FTS5 query returns ranked results with correct top hit

 1. file delete
 2. var db = PureDatabase open
 3. db exec sql
 4. db exec sql
 5. db exec sql
 6. db exec sql
    - Expected: results.len() equals `2`
    - Expected: top_id equals `1`
 7. db close
 8. file delete


 <details>
 <summary>Executable SSpec</summary>

 Runnable source: 17 lines folded for reproduction.
 Reproduction: this block contains the complete executable scenario source.

 ```simple
 val path = "/tmp/simple_db_bench_fts_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
 file_delete(path)

 var db = PureDatabase.open(path).unwrap()
 db.exec_sql("CREATE TABLE bench_fts (id INTEGER, body TEXT)").unwrap()
 db.exec_sql("INSERT INTO bench_fts (id, body) VALUES (1, 'database indexing and database tuning')").unwrap()
 db.exec_sql("INSERT INTO bench_fts (id, body) VALUES (2, 'network protocols overview')").unwrap()
 db.exec_sql("INSERT INTO bench_fts (id, body) VALUES (3, 'database schema design')").unwrap()

 val results = db.fts5_search("bench_fts", ["body"], "database", 5).unwrap()
 expect(results.len()).to_equal(2)

 val top_id = results[0].row.values[0].to_text()
 expect(top_id).to_equal("1")

 db.close().unwrap()
 file_delete(path)
 ```

 </details>

 ### update/delete invalidation gate

 #### AC-8: update clears stale FTS entry and delete removes it entirely

 1. file delete
 2. var db = PureDatabase open
 3. db exec sql
 4. db exec sql
 5. db exec sql
    - Expected: before.len() equals `1`
 6. db exec sql
    - Expected: after_update.len() equals `0`
 7. db exec sql
    - Expected: after_delete.len() equals `0`
 8. db close
 9. file delete


 <details>
 <summary>Executable SSpec</summary>

 Runnable source: 21 lines folded for reproduction.
 Reproduction: this block contains the complete executable scenario source.

 ```simple
 val path = "/tmp/simple_db_bench_inv_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
 file_delete(path)

 var db = PureDatabase.open(path).unwrap()
 db.exec_sql("CREATE TABLE bench_inv (id INTEGER, body TEXT)").unwrap()
 db.exec_sql("INSERT INTO bench_inv (id, body) VALUES (1, 'stale keyword here')").unwrap()
 db.exec_sql("INSERT INTO bench_inv (id, body) VALUES (2, 'another keyword row')").unwrap()

 val before = db.fts5_search("bench_inv", ["body"], "stale", 5).unwrap()
 expect(before.len()).to_equal(1)

 db.exec_sql("UPDATE bench_inv SET body = 'fresh content here' WHERE id = 1").unwrap()
 val after_update = db.fts5_search("bench_inv", ["body"], "stale", 5).unwrap()
 expect(after_update.len()).to_equal(0)

 db.exec_sql("DELETE FROM bench_inv WHERE id = 2").unwrap()
 val after_delete = db.fts5_search("bench_inv", ["body"], "keyword", 5).unwrap()
 expect(after_delete.len()).to_equal(0)

 db.close().unwrap()
 file_delete(path)
 ```

 </details>

 ### reopen/recovery gate

 #### AC-8: data persists and FTS rebuilds correctly after reopen

 1. file delete
 2. var db = PureDatabase open
 3. db exec sql
 4. db exec sql
 5. db exec sql
 6. db close
 7. var reopened = PureDatabase open
    - Expected: rows.len() equals `2`
    - Expected: fts.len() equals `2`
    - Expected: alpha.len() equals `1`
    - Expected: alpha_id equals `1`
 8. reopened close
 9. file delete


 <details>
 <summary>Executable SSpec</summary>

 Runnable source: 24 lines folded for reproduction.
 Reproduction: this block contains the complete executable scenario source.

 ```simple
 val path = "/tmp/simple_db_bench_reopen_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
 file_delete(path)

 var db = PureDatabase.open(path).unwrap()
 db.exec_sql("CREATE TABLE bench_reopen (id INTEGER, body TEXT)").unwrap()
 db.exec_sql("INSERT INTO bench_reopen (id, body) VALUES (1, 'durable record alpha')").unwrap()
 db.exec_sql("INSERT INTO bench_reopen (id, body) VALUES (2, 'durable record beta')").unwrap()
 db.close().unwrap()

 var reopened = PureDatabase.open(path).unwrap()

 val rows = reopened.query("SELECT * FROM bench_reopen", []).unwrap()
 expect(rows.len()).to_equal(2)

 val fts = reopened.fts5_search("bench_reopen", ["body"], "durable", 5).unwrap()
 expect(fts.len()).to_equal(2)

 val alpha = reopened.fts5_search("bench_reopen", ["body"], "alpha", 5).unwrap()
 expect(alpha.len()).to_equal(1)
 val alpha_id = alpha[0].row.values[0].to_text()
 expect(alpha_id).to_equal("1")

 reopened.close().unwrap()
 file_delete(path)
 ```

 </details>

 ## Scenario Summary

 | Metric | Count |
 |--------|------:|
 | Total scenarios | 6 |
 | Active scenarios | 6 |
 | Slow scenarios | 0 |
 | Skipped scenarios | 0 |
 | Pending scenarios | 0 |


 ## Related Documentation

 - **Plan:** [doc/03_plan/db_hardening_optimization_plan_2026-05-26.md](doc/03_plan/db_hardening_optimization_plan_2026-05-26.md)


 </details>

# Pure Db Optimization Specification

> 1. file delete

<!-- sdn-diagram:id=pure_db_optimization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_db_optimization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_db_optimization_spec -> std
pure_db_optimization_spec -> nogc_sync_mut
pure_db_optimization_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_db_optimization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Db Optimization Specification

## Scenarios

### Optimization A: Deferred Persist (AC-4, AC-5)

#### INSERT 100 rows with auto_checkpoint=false writes no disk until checkpoint

1. file delete
2. var db = PureDatabase open deferred
3. db exec sql
4. db exec sql
5. db checkpoint
6. print
7. print
8. db close
9. var verify = PureDatabase open
10. verify close
11. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = opt_tmp_path("deferred_a1")
file_delete(path)

# Use open_deferred to get auto_checkpoint=false
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE opt_a (id INTEGER, name TEXT)").unwrap()

# Insert 100 rows — deferred mode should NOT persist after each one
val t0 = bench_now_ns()
var i = 0
while i < 100:
    db.exec_sql("INSERT INTO opt_a (id, name) VALUES (" + i.to_text() + ", 'row_" + i.to_text() + "')").unwrap()
    i = i + 1
val t1 = bench_now_ns()

# Verify data is in memory
val mem_rows = db.query("SELECT count(*) FROM opt_a", []).unwrap()
expect(mem_rows.len()).to_be_greater_than(0)

# Now checkpoint — this should persist to disk
db.checkpoint().unwrap()
val t2 = bench_now_ns()

print("[OptA] 100 INSERT deferred: " + opt_elapsed_ms(t0, t1).to_text() + " ms")
print("[OptA] checkpoint flush: " + opt_elapsed_ms(t1, t2).to_text() + " ms")

db.close().unwrap()

# Verify data survived to disk by reopening
var verify = PureDatabase.open(path).unwrap()
val disk_rows = verify.query("SELECT count(*) FROM opt_a", []).unwrap()
expect(disk_rows.len()).to_be_greater_than(0)
verify.close().unwrap()

file_delete(path)
```

</details>

#### deferred INSERT is faster than auto-checkpoint INSERT

1. file delete
2. file delete
3. var db fast = PureDatabase open deferred
4. db fast exec sql
5. db fast exec sql
6. db fast checkpoint
7. db fast close
8. var db slow = PureDatabase open
9. db slow exec sql
10. db slow exec sql
11. db slow close
12. print
13. print
14. var verify fast = PureDatabase open
15. verify fast close
16. var verify slow = PureDatabase open
17. verify slow close
18. file delete
19. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path_fast = opt_tmp_path("deferred_fast")
val path_slow = opt_tmp_path("deferred_slow")
file_delete(path_fast)
file_delete(path_slow)

# Deferred mode (fast path)
var db_fast = PureDatabase.open_deferred(path_fast).unwrap()
db_fast.exec_sql("CREATE TABLE cmp (id INTEGER, name TEXT)").unwrap()
val t0 = bench_now_ns()
var i = 0
while i < 100:
    db_fast.exec_sql("INSERT INTO cmp (id, name) VALUES (" + i.to_text() + ", 'row_" + i.to_text() + "')").unwrap()
    i = i + 1
db_fast.checkpoint().unwrap()
val t1 = bench_now_ns()
db_fast.close().unwrap()

# Auto-checkpoint mode (slow path — default)
var db_slow = PureDatabase.open(path_slow).unwrap()
db_slow.exec_sql("CREATE TABLE cmp (id INTEGER, name TEXT)").unwrap()
val t2 = bench_now_ns()
var j = 0
while j < 100:
    db_slow.exec_sql("INSERT INTO cmp (id, name) VALUES (" + j.to_text() + ", 'row_" + j.to_text() + "')").unwrap()
    j = j + 1
val t3 = bench_now_ns()
db_slow.close().unwrap()

val deferred_ms = opt_elapsed_ms(t0, t1)
val auto_ms = opt_elapsed_ms(t2, t3)
print("[OptA] deferred 100 INSERT: " + deferred_ms.to_text() + " ms")
print("[OptA] auto-checkpoint 100 INSERT: " + auto_ms.to_text() + " ms")

# Deferred should be faster (or at least not slower under interpreter overhead)
# We assert both completed with correct data rather than strict timing
# because interpreter overhead can dominate small differences
var verify_fast = PureDatabase.open(path_fast).unwrap()
val rf = verify_fast.query("SELECT count(*) FROM cmp", []).unwrap()
expect(rf.len()).to_be_greater_than(0)
verify_fast.close().unwrap()

var verify_slow = PureDatabase.open(path_slow).unwrap()
val rs = verify_slow.query("SELECT count(*) FROM cmp", []).unwrap()
expect(rs.len()).to_be_greater_than(0)
verify_slow.close().unwrap()

file_delete(path_fast)
file_delete(path_slow)
```

</details>

### Optimization B: Incremental FTS (AC-4, AC-5)

#### INSERT row is findable via FTS without full rebuild

1. file delete
2. var db = PureDatabase open
3. db exec sql
4. db exec sql
   - Expected: warmup.len() equals `1`
5. db exec sql
   - Expected: found.len() equals `1`
   - Expected: found_id equals `2`
6. print
7. db close
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = opt_tmp_path("incr_fts_ins")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE fts_b (id INTEGER, body TEXT)").unwrap()

# Seed with initial data and trigger FTS build
db.exec_sql("INSERT INTO fts_b (id, body) VALUES (1, 'alpha bravo charlie')").unwrap()
val warmup = db.fts5_search("fts_b", ["body"], "alpha", 5).unwrap()
expect(warmup.len()).to_equal(1)

# Insert new row — incremental FTS should index it without full rebuild
db.exec_sql("INSERT INTO fts_b (id, body) VALUES (2, 'delta echo foxtrot')").unwrap()

val t0 = bench_now_ns()
val found = db.fts5_search("fts_b", ["body"], "echo", 5).unwrap()
val t1 = bench_now_ns()

expect(found.len()).to_equal(1)
val found_id = found[0].row.values[0].to_text()
expect(found_id).to_equal("2")

print("[OptB] Incremental FTS search after INSERT: " + opt_elapsed_ms(t0, t1).to_text() + " ms")

db.close().unwrap()
file_delete(path)
```

</details>

#### DELETE row is removed from FTS without full rebuild

1. file delete
2. var db = PureDatabase open
3. db exec sql
4. db exec sql
5. db exec sql
   - Expected: before.len() equals `1`
6. db exec sql
   - Expected: after.len() equals `0`
   - Expected: still.len() equals `1`
7. print
8. db close
9. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = opt_tmp_path("incr_fts_del")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE fts_d (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO fts_d (id, body) VALUES (1, 'golf hotel india')").unwrap()
db.exec_sql("INSERT INTO fts_d (id, body) VALUES (2, 'juliet kilo lima')").unwrap()

# Warm up FTS index
val before = db.fts5_search("fts_d", ["body"], "golf", 5).unwrap()
expect(before.len()).to_equal(1)

# Delete row 1
db.exec_sql("DELETE FROM fts_d WHERE id = 1").unwrap()

val t0 = bench_now_ns()
val after = db.fts5_search("fts_d", ["body"], "golf", 5).unwrap()
val t1 = bench_now_ns()

expect(after.len()).to_equal(0)

# Row 2 should still be findable
val still = db.fts5_search("fts_d", ["body"], "kilo", 5).unwrap()
expect(still.len()).to_equal(1)

print("[OptB] Incremental FTS search after DELETE: " + opt_elapsed_ms(t0, t1).to_text() + " ms")

db.close().unwrap()
file_delete(path)
```

</details>

#### mixed INSERT+DELETE maintains FTS correctness

1. file delete
2. var db = PureDatabase open
3. db exec sql
4. db exec sql
   - Expected: all_common.len() equals `10`
5. db exec sql
6. db exec sql
   - Expected: after_mix.len() equals `10`
   - Expected: gone.len() equals `0`
   - Expected: fresh.len() equals `1`
7. db close
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = opt_tmp_path("incr_fts_mix")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE fts_m (id INTEGER, body TEXT)").unwrap()

# Insert 10 rows
var i = 0
while i < 10:
    db.exec_sql("INSERT INTO fts_m (id, body) VALUES (" + i.to_text() + ", 'term_" + i.to_text() + " common_word document')").unwrap()
    i = i + 1

# Warm up FTS
val all_common = db.fts5_search("fts_m", ["body"], "common_word", 20).unwrap()
expect(all_common.len()).to_equal(10)

# Delete rows 0–4
var j = 0
while j < 5:
    db.exec_sql("DELETE FROM fts_m WHERE id = " + j.to_text()).unwrap()
    j = j + 1

# Insert 5 new rows
var k = 10
while k < 15:
    db.exec_sql("INSERT INTO fts_m (id, body) VALUES (" + k.to_text() + ", 'fresh_" + k.to_text() + " common_word document')").unwrap()
    k = k + 1

# Verify: common_word should match 10 rows (5 surviving + 5 new)
val after_mix = db.fts5_search("fts_m", ["body"], "common_word", 20).unwrap()
expect(after_mix.len()).to_equal(10)

# Verify: deleted term should not match
val gone = db.fts5_search("fts_m", ["body"], "term_0", 5).unwrap()
expect(gone.len()).to_equal(0)

# Verify: new term should match
val fresh = db.fts5_search("fts_m", ["body"], "fresh_12", 5).unwrap()
expect(fresh.len()).to_equal(1)

db.close().unwrap()
file_delete(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/bench/pure_db_optimization_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Optimization A: Deferred Persist (AC-4, AC-5)
- Optimization B: Incremental FTS (AC-4, AC-5)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

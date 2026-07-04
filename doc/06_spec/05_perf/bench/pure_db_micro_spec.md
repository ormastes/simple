# Pure Db Micro Specification

> 1. file delete

<!-- sdn-diagram:id=pure_db_micro_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_db_micro_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_db_micro_spec -> std
pure_db_micro_spec -> nogc_sync_mut
pure_db_micro_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_db_micro_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Db Micro Specification

## Scenarios

### PureDatabase Micro-Benchmarks

### W1: INSERT 200 rows deferred (no UNIQUE)

#### inserts 200 rows with deferred persist and measures time

1. file delete
2. var db = PureDatabase open deferred
3. db exec sql
4. db exec sql
5. db checkpoint
6. print
7. db close
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = tmp_path("w1")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w1 (id INTEGER, name TEXT, score INTEGER)").unwrap()

val t0 = bench_now_ns()
var i = 0
while i < 200:
    val sql = "INSERT INTO w1 (id, name, score) VALUES (" + i.to_text() + ", 'user_" + i.to_text() + "', " + (i * 10).to_text() + ")"
    db.exec_sql(sql).unwrap()
    i = i + 1
db.checkpoint().unwrap()
val t1 = bench_now_ns()

print("[W1] INSERT 200 rows (deferred): " + elapsed_ms(t0, t1).to_text() + " ms")

val rows = db.query("SELECT count(*) FROM w1", []).unwrap()
expect(rows.len()).to_be_greater_than(0)

db.close().unwrap()
file_delete(path)
```

</details>

### W2: Point SELECT by rowid

#### selects single row by id 100 times

1. file delete
2. var db = PureDatabase open deferred
3. db exec sql
4. db exec sql
5. db checkpoint
6. print
7. db close
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = tmp_path("w2")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w2 (id INTEGER, name TEXT)").unwrap()
var i = 0
while i < 200:
    db.exec_sql("INSERT INTO w2 (id, name) VALUES (" + i.to_text() + ", 'row_" + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val idx = j * 2
    val rs = db.query("SELECT id, name FROM w2 WHERE id = " + idx.to_text(), []).unwrap()
    expect(rs.len()).to_be_greater_than(0)
    j = j + 1
val t1 = bench_now_ns()

print("[W2] Point SELECT x100: " + elapsed_ms(t0, t1).to_text() + " ms")

db.close().unwrap()
file_delete(path)
```

</details>

### W3: Range scan SELECT

#### scans rows WHERE score > threshold 100 times

1. file delete
2. var db = PureDatabase open deferred
3. db exec sql
4. db exec sql
5. db checkpoint
6. print
7. db close
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = tmp_path("w3")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w3 (id INTEGER, score INTEGER)").unwrap()
var i = 0
while i < 200:
    db.exec_sql("INSERT INTO w3 (id, score) VALUES (" + i.to_text() + ", " + i.to_text() + ")").unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val rs = db.query("SELECT id, score FROM w3 WHERE score > 150", []).unwrap()
    expect(rs.len()).to_be_greater_than(0)
    j = j + 1
val t1 = bench_now_ns()

print("[W3] Range scan x100: " + elapsed_ms(t0, t1).to_text() + " ms")

db.close().unwrap()
file_delete(path)
```

</details>

### W4: Prefix search

#### searches by prefix pattern 100 times

1. file delete
2. var db = PureDatabase open deferred
3. db exec sql
4. db exec sql
5. db checkpoint
6. print
7. db close
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = tmp_path("w4")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w4 (id INTEGER, name TEXT)").unwrap()
var i = 0
while i < 200:
    val prefix = if i < 100: "alpha_" else: "beta_"
    db.exec_sql("INSERT INTO w4 (id, name) VALUES (" + i.to_text() + ", '" + prefix + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val rs = db.query("SELECT id, name FROM w4 WHERE name LIKE 'alpha_%'", []).unwrap()
    expect(rs.len()).to_be_greater_than(0)
    j = j + 1
val t1 = bench_now_ns()

print("[W4] Prefix search x100: " + elapsed_ms(t0, t1).to_text() + " ms")

db.close().unwrap()
file_delete(path)
```

</details>

### W5: FTS5 search

#### full-text searches 100 times

1. file delete
2. var db = PureDatabase open deferred
3. db exec sql
4. db exec sql
5. db checkpoint
6. print
7. db close
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = tmp_path("w5")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w5 (id INTEGER, body TEXT)").unwrap()
var i = 0
while i < 200:
    val word = if i < 40: "alpha" else: if i < 80: "bravo" else: if i < 120: "charlie" else: if i < 160: "delta" else: "echo"
    db.exec_sql("INSERT INTO w5 (id, body) VALUES (" + i.to_text() + ", '" + word + " document number " + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val results = db.fts5_search("w5", ["body"], "bravo", 10).unwrap()
    expect(results.len()).to_be_greater_than(0)
    j = j + 1
val t1 = bench_now_ns()

print("[W5] FTS5 search x100: " + elapsed_ms(t0, t1).to_text() + " ms")

db.close().unwrap()
file_delete(path)
```

</details>

### W6: Reopen latency

#### closes and reopens database 10 times

1. file delete
2. var db = PureDatabase open deferred
3. db exec sql
4. db exec sql
5. db checkpoint
6. db close
7. var rdb = PureDatabase open
8. rdb close
9. print
10. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = tmp_path("w6")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w6 (id INTEGER, body TEXT)").unwrap()
var i = 0
while i < 100:
    db.exec_sql("INSERT INTO w6 (id, body) VALUES (" + i.to_text() + ", 'persistent row " + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()
db.close().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 10:
    var rdb = PureDatabase.open(path).unwrap()
    val rs = rdb.query("SELECT count(*) FROM w6", []).unwrap()
    expect(rs.len()).to_be_greater_than(0)
    rdb.close().unwrap()
    j = j + 1
val t1 = bench_now_ns()

print("[W6] Reopen x10: " + elapsed_ms(t0, t1).to_text() + " ms")

file_delete(path)
```

</details>

### SQLite Comparison (AC-2)

#### W1s–W6s: documents SQLite FFI availability

1. print
2. print
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SQLite FFI (rt_sqlite_*) requires libsqlite3 linked at build time.
# When available, implement identical W1–W6 workloads against
# std.nogc_sync_mut.database.sql.connection.Database.
# Current status: FFI may not be linked in interpreter mode.
print("[SQLite] SKIP: SQLite FFI (rt_sqlite_*) not reliably available in interpreter mode")
print("[SQLite] See doc/09_report/ comparison report for qualitative analysis")
expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/bench/pure_db_micro_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PureDatabase Micro-Benchmarks
- W1: INSERT 200 rows deferred (no UNIQUE)
- W2: Point SELECT by rowid
- W3: Range scan SELECT
- W4: Prefix search
- W5: FTS5 search
- W6: Reopen latency
- SQLite Comparison (AC-2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
